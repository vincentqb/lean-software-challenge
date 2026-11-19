# Lean Software Challenge

1. In a copy of `Examples/ConstantFolding`, state each hole in `Challenge.lean` as
   `def … := sorry`, each headline as `theorem … := sorry`, and a `@[kills headline]` theorem
   for each headline.
2. `lake build`
3. Agents write the CoreCode, WorldCode and Solution modules.
4. `lake lint`
5. `lake test`
6. `lake comparator`
7. `lake exe grade <commit>`
