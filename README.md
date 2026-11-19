# Lean Software Challenge

1. Copy `Examples/ConstantFolding`, and replace its `require software_challenge from "../.."` with
   `require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"`.
2. In `Challenge.lean`, state each hole as `def … := sorry`, each headline as a `theorem … := sorry`,
   and, for each headline, a `@[kills headline]` theorem.
3. `lake build`
4. Agents write the CoreCode, WorldCode and Solution modules.
5. `lake lint`: 0 when complete, 2 while items are pending, 1 on an error.
6. `lake test`
7. `lake comparator`
8. `lake exe grade <commit>`: 0 accepts, 1 refuses, 3 cannot judge.
