# Lean Software Challenge

1. In a copy of `Examples/ConstantFolding`, state each hole in `Challenge.lean` as
   `def … := sorry`, each headline as `theorem … := sorry`, and a `@[kills headline]` theorem
   for each headline; state each world claim as an `axiom` about an `@[extern] opaque` function,
   with one `@[consistent]` theorem.
2. `lake build`
3. Agents write the modules that define the holes, the Solution module, and a `@[tests claim]`
   test of each world claim.
4. `lake lint`
5. `lake test`
6. `lake comparator`
7. `lake exe grade <commit>`
