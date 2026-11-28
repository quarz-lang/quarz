/* The Quarz native ABI, version 1.0 (docs/15), for a cog's native code
 * written in C. The source of truth is quarz-ext's `sys` module (Rust);
 * this copy is checked against it by quarz-ext's tests: every struct's
 * size and offsets and every constant.
 *
 * Only fixed-width types cross the boundary. Structs have natural
 * alignment. QzApi, QzModule and QzMethod grow only at their end; their
 * first fields never change. */
#ifndef QUARZ_EXT_H
#define QUARZ_EXT_H

#include <stddef.h>
#include <stdint.h>

#define QZ_ABI_MAJOR 1u
#define QZ_ABI_MINOR 1u

typedef uint64_t QzValue;   /* a handle; 0 is no value */
typedef int32_t QzStatus;
typedef uint32_t QzKind;
typedef uint8_t QzBool;     /* 0 false, anything else true */

#define QZ_OK 0
#define QZ_RAISED 1

#define QZ_NIL 0u
#define QZ_BOOL 1u
#define QZ_INT 2u
#define QZ_FLOAT 3u
#define QZ_STRING 4u
#define QZ_BYTES 5u
#define QZ_SYMBOL 6u
#define QZ_ARRAY 7u
#define QZ_HASH 8u
#define QZ_OTHER 9u
#define QZ_INVALID 0xFFFFFFFFu

typedef struct QzCall QzCall;

typedef QzStatus (*QzEntry)(QzCall *cx, QzValue recv, const QzValue *args,
                            size_t nargs, QzValue blk, QzValue *out);

typedef struct QzMethod {
    const uint8_t *key;
    size_t key_len;
    QzEntry entry;
} QzMethod;

typedef struct QzModule {
    uint32_t abi_major;
    uint32_t abi_minor;
    const QzMethod *methods;
    size_t n_methods;
    size_t method_size;
} QzModule;

typedef struct QzApi {
    uint32_t abi_major;
    uint32_t abi_minor;
    size_t size;

    QzKind (*kind)(QzCall *, QzValue);

    QzValue (*nil)(QzCall *);
    QzValue (*bool_new)(QzCall *, QzBool);
    QzStatus (*bool_get)(QzCall *, QzValue, QzBool *);
    QzValue (*int_new)(QzCall *, int64_t);
    QzStatus (*int_get)(QzCall *, QzValue, int64_t *);
    QzValue (*float_new)(QzCall *, double);
    QzStatus (*float_get)(QzCall *, QzValue, double *);

    QzStatus (*string_new)(QzCall *, const uint8_t *, size_t, QzValue *);
    QzStatus (*string_get)(QzCall *, QzValue, const uint8_t **, size_t *);
    QzValue (*bytes_new)(QzCall *, const uint8_t *, size_t);
    QzValue (*bytes_new_uninit)(QzCall *, size_t, uint8_t **);
    QzStatus (*bytes_get)(QzCall *, QzValue, const uint8_t **, size_t *);
    QzStatus (*symbol_new)(QzCall *, const uint8_t *, size_t, QzValue *);
    QzStatus (*symbol_get)(QzCall *, QzValue, const uint8_t **, size_t *);

    QzStatus (*array_len)(QzCall *, QzValue, size_t *);
    QzStatus (*array_get)(QzCall *, QzValue, size_t, QzValue *);
    QzValue (*array_new)(QzCall *, size_t);
    QzStatus (*array_push)(QzCall *, QzValue, QzValue);

    QzStatus (*hash_len)(QzCall *, QzValue, size_t *);
    QzStatus (*hash_get)(QzCall *, QzValue, QzValue, QzValue *, QzBool *);
    QzStatus (*hash_entry)(QzCall *, QzValue, size_t, QzValue *, QzValue *);
    QzValue (*hash_new)(QzCall *);
    QzStatus (*hash_put)(QzCall *, QzValue, QzValue, QzValue);

    QzStatus (*exception_class)(QzCall *, const uint8_t *, size_t, QzValue *);
    QzStatus (*raise)(QzCall *, QzValue, const uint8_t *, size_t);

    void (*release)(QzCall *, QzValue);

    /* ABI 1.1 */
    QzStatus (*call_block)(QzCall *, QzValue, const QzValue *, size_t, QzValue *);
} QzApi;

/* A cog's only export is its init, `qz_cog_init_<cog>`, the cog's name
 * with each `_` as `__` and each `-` as `_h`. */
typedef const QzModule *(*QzInit)(const QzApi *api);

#endif
