# 15. Native code in cogs: the ABI

A cog can implement some of its methods in Rust (#677): it declares them `native def` in Quarz, and its native package implements them against a stable C ABI. Rust code uses the safe wrapper crate `quarz-ext`, whose major version is the ABI's, as a git dependency on the quarz repository ([10-cogs.md](10-cogs.md) §11); C code uses `quarz_ext.h`. Values cross as opaque handles, never as the runtime's own values, so the ABI does not change when the runtime does.

**Status:** `quarz run` and `quarz test` build and load a native cog's package; `quarz build` links them into the executable. How a cog declares its native code, and how `quarz` builds and keeps it, is [10-cogs.md](10-cogs.md) §11. This page is the ABI: what a cog's native code sees, a promise from its first release.

## What a cog's `native def` may declare

- **Where:** a `native def` is allowed only in a cog whose manifest declares native code (`World::native_cog`); anywhere else it is an error (#1198). It is bound to that cog's own module's entry of its key, never to a standard native.
- **Parameters:** positional and keyword-only ones (required, or with a literal default), and a block. Refused at the declaration: `*rest`, `**rest`, and a default that is not a literal.
- **Overloads:** a cog's native has no overload: its entry is found by its key (`Owner#name`), which overloads share. A method of the same name and side is refused beside it in the class's own methods (a standard one too: `extension String; native def upcase(x: Int)` would overload `String#upcase`) and in the same cog's extensions of the class, in one block or several, in one file or several. Another cog's method of that name, or the application's, is no overload: it is bound on its own (to its own cog's module, or to its body).
- **Compile time:** a cog's native never runs at compile time. It is refused by its kind (`RtMethod::ext`), whatever its key or its owner's name: a cog's `extension String; native def` is not "pure" for being on `String`.

## Types

```c
typedef uint64_t QzValue;      /* an opaque handle; 0 is "no value" (no block, nothing yet) */
typedef struct QzCall QzCall;  /* opaque: one call of one native */
typedef int32_t  QzStatus;     /* QZ_OK = 0, QZ_RAISED = 1 */
typedef uint32_t QzKind;       /* QZ_NIL 0, QZ_BOOL 1, QZ_INT 2, QZ_FLOAT 3, QZ_STRING 4, QZ_BYTES 5,
                                  QZ_SYMBOL 6, QZ_ARRAY 7, QZ_HASH 8, QZ_OTHER 9; more may come */
typedef uint8_t  QzBool;       /* 0 false, 1 true; any other value from a cog reads as true */
```

Only fixed-width types cross the boundary: no C `enum`, no `bool`, no `int`. Structs are `#[repr(C)]` with natural alignment, no packing.

## The entry, the module, the init

```c
typedef QzStatus (*QzEntry)(QzCall *cx, QzValue recv, const QzValue *args,
                            size_t nargs, QzValue blk, QzValue *out);

typedef struct { const char *key; size_t key_len; QzEntry entry; } QzMethod;
typedef struct { uint32_t abi_major, abi_minor;
                 const QzMethod *methods; size_t n_methods;
                 size_t method_size;      /* sizeof(QzMethod) as the cog knows it: the array's stride */
               } QzModule;

/* The cog's only export, named by the wrapper's macro. */
const QzModule *qz_cog_init_<cog>(const QzApi *api);
```

**`<cog>`, the cog's name encoded:** each `_` becomes `__`, each `-` becomes `_h` (`zlib-ng` → `qz_cog_init_zlib_hng`, `zlib_ng` → `qz_cog_init_zlib__ng`). Every cog name (`[a-z][a-z0-9_-]*`) is legal, and two cogs never share a symbol. The wrapper's macro writes the symbol; an author never types it.

**What may grow:** `QzApi` and `QzModule` grow only at their end, and the runtime reads only the fields the module's own `abi_minor` defines. `QzMethod` is an array element whose stride is `method_size`, so a later minor can append fields to it too.

**The prefix that never changes, whatever the major:** `abi_major, abi_minor, size` of `QzApi`, and `abi_major, abi_minor` of `QzModule`. Init can read the API's major, and quarz the module's, before anything else is trusted.

**The entry:**
- `blk` is 0 when no block was given. Calling it is ABI 1.1 (`call_block`, below); the parameter is in the signature from 1.0.
- On `QZ_OK`, `*out` holds the result: a handle the call made, or one it was lent. An entry declared `-> Void` sets `*out` to nil or leaves it 0.
- `args` holds every declared parameter in declaration order, positional ones first, then keyword-only ones (`Zlib.deflate(data, *, level: Int = 6)` gets `args[0]` = data, `args[1]` = level). The runtime binds each argument to its position, whether passed positionally or by keyword, and fills in the declared default of one the caller left out. So `nargs` is always the declared count. (A standard native reads its keyword-only parameters from `Args::kw`; a cog's entry never sees keywords.)
- In 1.0 a cog's `native def` may have positional parameters, keyword-only parameters (required, or with a default), and a block. A default must be a literal (nil, a Bool, an Int, a Float, a Symbol): what the runtime fills in. These are refused at the declaration: a non-literal default, a splat, `**rest`.

**The module:**
- Each key is `Owner#name` or `Owner.name`, with the owner's full name as the cog declares it.
- A key the cog's declarations do not have is an error when the library is loaded, and so is a declared `native def` the module does not provide. Both errors name the cog and the key.

**Init:**
- It returns null to refuse, when `api->abi_major` differs from its own.
- It is called once per process, before any entry, however many workers run.
- It may keep `api` but must not call it.
- A cog's library is never unloaded.
- Entries are called concurrently from several workers, so a cog's global state must be thread-safe. The wrapper requires `Sync` of what it keeps.

## Status and errors

- Every API function that can fail returns a `QzStatus`. On `QZ_RAISED`, an exception is pending in `cx` and the entry should return `QZ_RAISED` at once. The wrapper's `?` does this.
- An entry that returns `QZ_RAISED` with no exception pending is a contract error: `RuntimeError`, with a message naming the key. So is one returning `QZ_OK` without setting `*out` when its result is not `Void` (or `Nil`), and one returning a status that is neither `QZ_OK` nor `QZ_RAISED`.
- An entry that returns `QZ_OK` with an exception pending raises that exception.
- The result's class is always tested against the declaration, on every call (`Interp::native_result_test`, the test `QUARZ_VERIFY` runs for standard natives). A mismatch raises `TypeError`: "native `Demo.wrong` returned a value of class String, but its declared result is Int".
- A wrong kind (`int_get` on a `String`) raises `TypeError`, naming what was expected. An `Int` that does not fit 64 bits (`Integer`) raises `RangeError` in `int_get`.
- Makers (`int_new` ...) cannot fail; out of memory aborts, as the runtime does.
- **With an exception pending,** every status function returns `QZ_RAISED` without acting, every maker returns 0, and `raise` keeps the first exception. A cog that ignores a status can neither overwrite nor lose the exception. `release` on an invalid or already released handle does nothing.
- A panic is caught by the wrapper at every entry and raised as `NativePanic` (a `StandardError`, decided on #677), with the panic's message. The cog is built with `panic = "unwind"`.

**What the cog is trusted for.** Every misuse of a handle or a value through the API is refused with an exception: a wrong kind, a stale or foreign handle, a change to a value the call did not make, a key or a class the ABI does not take. Three things are not checked:
- The result's type beyond its top level. The result's own class is tested on every call, but nothing tests the elements of a returned collection (an `Array[Int]` holding a `String`).
- Anything kept past the call's return: a `QzCall`, a handle or a lent pointer. Using one afterwards is undefined behaviour, as is a cog's own memory error.
- A write through `bytes_new_uninit`'s pointer after the value was first used (given to `call_block`, put into a collection, or the call returned): undefined behaviour (below).

## The API, ABI 1.0 (`QzApi`, `#[repr(C)]`, append-only)

```c
typedef struct QzApi {
  uint32_t abi_major, abi_minor;   /* 1, 1 */
  size_t   size;                   /* sizeof(QzApi) as this runtime knows it */

  QzKind   (*kind)(QzCall*, QzValue v);   /* 0xFFFFFFFF for an invalid handle */

  QzValue  (*nil)(QzCall*);
  QzValue  (*bool_new)(QzCall*, QzBool b);
  QzStatus (*bool_get)(QzCall*, QzValue v, QzBool *out);
  QzValue  (*int_new)(QzCall*, int64_t i);
  QzStatus (*int_get)(QzCall*, QzValue v, int64_t *out);
  QzValue  (*float_new)(QzCall*, double f);
  QzStatus (*float_get)(QzCall*, QzValue v, double *out);   /* a Float only: no Int */

  QzStatus (*string_new)(QzCall*, const uint8_t *p, size_t n, QzValue *out); /* ArgumentError unless UTF-8 */
  QzStatus (*string_get)(QzCall*, QzValue v, const uint8_t **p, size_t *n);
  QzValue  (*bytes_new)(QzCall*, const uint8_t *p, size_t n);
  QzValue  (*bytes_new_uninit)(QzCall*, size_t n, uint8_t **p); /* n zeroed bytes, writable until first used */
  QzStatus (*bytes_get)(QzCall*, QzValue v, const uint8_t **p, size_t *n);
  QzStatus (*symbol_new)(QzCall*, const uint8_t *p, size_t n, QzValue *out); /* UTF-8 */
  QzStatus (*symbol_get)(QzCall*, QzValue v, const uint8_t **p, size_t *n);

  QzStatus (*array_len)(QzCall*, QzValue a, size_t *out);
  QzStatus (*array_get)(QzCall*, QzValue a, size_t i, QzValue *out);  /* IndexError */
  QzValue  (*array_new)(QzCall*, size_t capacity);
  QzStatus (*array_push)(QzCall*, QzValue a, QzValue v);

  QzStatus (*hash_len)(QzCall*, QzValue h, size_t *out);
  QzStatus (*hash_get)(QzCall*, QzValue h, QzValue key, QzValue *out, QzBool *found);
  QzStatus (*hash_entry)(QzCall*, QzValue h, size_t i, QzValue *key, QzValue *value); /* insertion order; IndexError */
  QzValue  (*hash_new)(QzCall*);
  QzStatus (*hash_put)(QzCall*, QzValue h, QzValue key, QzValue value);

  QzStatus (*exception_class)(QzCall*, const uint8_t *name, size_t n, QzValue *out);
  QzStatus (*raise)(QzCall*, QzValue cls, const uint8_t *msg, size_t n); /* returns QZ_RAISED */

  void     (*release)(QzCall*, QzValue v);

  /* ABI 1.1 */
  QzStatus (*call_block)(QzCall*, QzValue blk, const QzValue *args, size_t nargs, QzValue *out);
} QzApi;
```

Notes on the functions:
- `hash_get` and `hash_put` compare keys as `Hash` does. Both take only `Int`, `String`, `Bytes`, `Symbol` or nil as a key in 1.0, so that no Quarz code (a key's own `==` or `hash`) runs inside an API call. Another key kind raises `TypeError`.
- `hash_entry(i)` is O(1) for every hash: both representations (`ValueMap`, and `IntMap` for `Int` to `Int`) are `IndexMap`s, dense after removals. Iterating `0..len` is linear.
- `exception_class` resolves a class by its full name in the program (`"ArgumentError"`, `"Zlib::DataError"`). It accepts only an exception class that the built-in path can construct from a message alone. The class is concrete and not generic: an abstract class has no instances, and a generic one's would carry no type arguments. No class from it up to the nearest built-in exception class declares an `initialize` or a field, since running one would be Quarz code and skipping it would leave a field uninitialized. Only a class body can declare either: a module and an extension can declare neither an `initialize` nor a field. Otherwise it raises `ArgumentError`, naming the class and the reason. Its handle is the call's.
- `raise` makes the exception by that path, with `msg` as its message (UTF-8; invalid bytes are replaced).
- `bytes_new_uninit` gives `n` zeroed bytes to write through `*p`. They may be written until the value is first used as anything but the result to be: passed to `call_block`, pushed or put into a collection (`array_push`, `hash_put`, as an element, key or value), or the entry returns, whichever comes first. From then on, Quarz may see the bytes, keep them, or send them to another worker, and holds them as immutable. Writing through `*p` after that is undefined behaviour (a data race once they cross workers). What is left unwritten stays zero. The wrapper's `bytes_with` cannot break this rule: `fill` ends before the value exists.
- `kind`:
  - an `Integer` beyond 64 bits is `QZ_INT`, and `int_get` on it raises `RangeError`;
  - a class value (the receiver of an `Owner.name` method) is `QZ_OTHER`;
  - `Bytes::Secret` is `QZ_OTHER`, and `bytes_get` on it raises `TypeError`: its bytes are never exposed in 1.0;
  - a handle that is not one of the call's (another call's, or a made one released) is `QZ_INVALID` (`0xFFFFFFFF`), never an error. The wrapper's `Kind` has `Invalid` for it, and `Other` for a kind a later minor version adds.

## Handle rules

1. **Lent handles** (`recv`, `args[i]`, `blk`) are valid for the call; `release` on one does nothing.
2. **Made handles** (every `_new`, `array_get`, `hash_get`, `hash_entry`, `exception_class`) belong to the call. All are released when the entry returns, except the one in `*out`, which the runtime takes. `release` lets go of one early (a long loop of `array_get`s), unless bytes of it were lent (rule 5): that one is kept until the entry returns, and `release` on it does nothing.
3. **No handle outlives its call or leaves its thread.** `QzCall` is not `Send`; a handle from another call is detected (the call's serial in the handle, unique in the process from 1.1, so that a handle carried to another call on any thread is refused) and raises `TypeError`, never undefined behaviour. A value kept across calls is a native-data object, in the second scope.
4. **Values are immutable.** `array_push` and `hash_put` accept only a collection this call made and has not yet given away (put into another collection, or set as `*out`); on anything else they raise `TypeError`. Nothing mutates a lent value.
5. **Borrowed pointers** (`string_get`, `bytes_get`, `symbol_get`, and `bytes_new_uninit`'s) stay valid until the entry returns, whatever is released (`bytes_new_uninit`'s may be written only until the value is first used, above): a made value whose bytes were lent is kept to the end of the call. The bytes are not NUL-terminated, and `string_get`'s are UTF-8. `symbol_get` keeps one name per symbol for the call, so asking for the same symbols in a loop does not grow the call's memory.
6. **Lent values are the call's own arguments**, moved into its frame: no copy. A made handle holds a counted reference in the call's frame.
7. **The values a cog can make:** the literal classes and exceptions (always live under `shake`). Objects of its own classes come in the second scope, by a class the method declares in its result type (`RtMethod::makes`).

## The header and the Rust definitions

The source is the Rust `quarz_ext::sys` module (`crates/quarz-ext/src/sys.rs`). `crates/quarz-ext/include/quarz_ext.h` is written by hand beside it. A test compiles the header with `_Static_assert`s on every struct's size and every field's offset, the values Rust computes (`size_of`, `offset_of!`), and on every constant, so the two cannot drift. Another test pins ABI 1.0's layout by numbers (`tests/abi10.rs`: the constants, every struct's offsets, `QzApi`'s functions in their order), so that a change that is not append-only fails even when both sides change together: cogs depend on `quarz-ext` by git at any commit.

## Calling the block (ABI 1.1)

`call_block(cx, blk, args, nargs, out)` calls the method's block with `nargs` handles of the call. Its value is a made handle of the call. The wrapper's form is `Call::call_block(&[..])`.

- **It runs on the calling task**, as a standard native's `yield` does: `next` gives the block's value.
- **The block may suspend the task** (a `Channel` receive, IO, `Task.sleep`). The native's frames stay where they are on the task's own stack, and the task resumes on the same worker, so every handle and lent pointer of the call stays valid across it.
- **What the block raises** is pending in the call. So is a `break` or a `return` out of the block, carried through the native to its caller. `call_block` returns `QZ_RAISED`, and the entry returns at once. The wrapper's `?` does this; a cog cannot catch the flow, and every later status function returns `QZ_RAISED` while it is pending. A task cancelled while the block waits is raised in at its suspension point, and so reaches the native the same way.
- **Re-entrancy.** While a native waits in `call_block`, the same cog's natives (the same one included) can be entered again, each call with a frame of its own: on the same thread (by the block, or by another task of that worker while the block waits), and on other workers. A cog's global and thread-local state must allow it: hold no lock and no `RefCell` borrow across `call_block`, and assume no "one call at a time". A lock held across it can deadlock with another task of the same worker.
- **A program that ends while a task waits in a native's block.** The task is not resumed and its stack is not unwound, so the destructors of the cog's frames on it do not run, as at a process's `exit`. Flush and unlock before `call_block`, not in a destructor across it. Nothing aborts: an interpreter dropped with such a task forgets its stack instead of unwinding it.

## Versioning

- quarz refuses a module whose `abi_major` is not its own, or whose `abi_minor` is greater than its own. The error names the cog and both versions.
- `QzApi` only grows: a minor version appends fields, and `size` tells a cog how much exists.
- The wrapper crate's major version is the ABI major, and its minor at least the ABI minor it uses.
- 1.1 (the second scope) adds `call_block`, native-data objects (`object_new`, `object_data`, with a drop function in `QzModule`'s class list) and `blocking`. `call_block` is in; the rest come with the same minor, before a release.
