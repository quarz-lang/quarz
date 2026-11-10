# Review checklist

For the fresh subagent that reviews a branch's diff before the pull
request leaves draft (CLAUDE.md, "Before committing"). Report each
finding as a program with the two answers (the checker's and the
runtime's, the VM's and the compiled program's, or the branch's and
main's); correctness only.

1. **Second computation.** Does the diff compute a relation an existing
   function already decides (subtyping, ancestors and resolution order,
   override, conformance and witnesses, signature equality, what a type
   test can see, block binding, object layout; CLAUDE.md "One computation
   per relation")? Name the existing function and say whether the new
   code could call it.
2. **Scope.** For each new check, is its scope the scope of the run-time
   behaviour it guards: lexical versus global, the class versus its
   subclasses, a class target versus a module target, one cog versus
   another cog?
3. **Escape routes.** Can the guarded value reach the code by another
   path: a field, a tuple or array element, a lambda capture, `rescue`,
   a pattern, a `Type[M]` value, `super`, an inference variable resolved
   later, a synthesized method (`attr_*`, a `data` accessor, a generated
   method), a built-in value class (`Time`, `Bytes`, ...)?
4. **Fallbacks.** Any `else` or `None =>` at run time that supplies an
   answer where a record is missing, instead of an internal error?
5. **Both backends, against main.** Run every probe interpreted and
   compiled with `QUARZ_VERIFY=moves`; run the fixtures of the area and
   `quarz check` over the tracked `.qz` files with the branch's binary
   and with main's, and list what changed verdict.
6. **Matrix.** For a change to one of the relations above: are the axes
   of CLAUDE.md "Tests" covered, and are the expected values derived from
   the rules rather than from a run?
