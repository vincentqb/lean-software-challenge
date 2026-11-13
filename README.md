# Lean Software Challenge

A repository that uses this library is a challenge: implement code that does what its headline
theorems say. You own the challenge, and agents submit solutions made of code and proofs.
Requires **Lean 4.35.0**.

## What an accepted solution guarantees

- **Every headline is proved.** The kernel checked each proof, and `lake comparator` replays it.
- **The code that runs is the code proved.** CoreSpec and CoreCode are pure, their recursion is
  structural, well-founded, or a `partial_fixpoint` hole whose return a headline states, foreign
  code enters only through `@[extern] opaque` declarations in WorldSpec, CoreCode never calls
  it, and `main` reaches every hole.
- **Every headline can fail.** A kill proves it rejects a wrong implementation.
- **Every assumption is named and tested.** A headline assumes only the world claims it takes as
  hypotheses, and `lake test` runs at least one `Check` of each.
- **What is claimed did not change.** A build fails when a file on the report's `Owned:` line
  differs from `owned.lock`, and `grade` refuses a candidate that edits one.

## Files

| File | Contains | Approved by |
|---|---|---|
| `Challenge.lean` | the headlines, holes, and kills, stated with `sorry` | you |
| `comparator.json` | the headlines, kills, and holes `lake comparator` checks, and the `terminates` headlines | you |
| `MyApp/CoreSpec.lean` | types and the reference meaning headlines are stated in | you |
| `MyApp/WorldSpec.lean` | `@[extern] opaque` declarations for foreign code, and the world claims about them | you |
| `owned.lock` | a hash of each file above, which the first build records | you |
| `MyApp/CoreCode.lean` | pure code: public interface, private helpers, and their proofs | agents |
| `MyApp/WorldCode.lean` | IO, calls to foreign code, `main`, and the `Check`s of world claims | agents |
| `MyApp/Solution.lean` | proofs of the headlines and kills | agents |

Headlines are end-to-end theorems: they say what the program does in terms of the spec,
assuming only named claims. In the [template](Examples/ConstantFolding), whose challenge is
[`Challenge.lean`](Examples/ConstantFolding/Challenge.lean), `output_correct` says the
output is the true value of an expression, assuming native addition is correct.

## Syntax

```lean
meta import SoftwareChallenge

/-- The adder agrees with `Nat.add`. A different sum for any pair falsifies it. -/
WorldClaim AddAgrees (add : Nat → Nat → Nat) := ∀ a b, add a b = a + b

Check AddAgrees nativeAdd : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71
Check AddAgrees nativeAdd := do
  for a in [0, 1, 2 ^ 64] do
    unless nativeAdd a 7 - a == 7 do throw (.userError s!"nativeAdd {a} 7 disagrees")

theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :
    output e = toString (eval (fun _ => 0) e)
theorem output_correct_rejects_suffix :
    ¬ (AddAgrees Nat.add → ∀ e : Expr,
      (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e))
```

- `WorldClaim Name := P`, in a WorldSpec module, names an assumption about the world; its doc
  comment names the observation that would falsify it, and the foreign code it constrains is a
  parameter.
- `Check`, in a WorldCode module, tests a world claim against the real foreign code: the first
  form one instance that must follow from the claim, the second any IO action, which throws to
  fail. The build only registers checks; `lake test` runs them all.
- A headline takes the world claims it rests on as hypotheses; the report lists them after
  `assumes`, with how many checks each has.
- A kill is `¬` a headline with its holes and WorldSpec foreign constants replaced by wrong
  ones, marked `@[kills headline]`; every headline needs one.

## Setup

In `lakefile.lean`:

```lean
package «my_app» where
  testDriver := "software_challenge/test_challenge"

require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
lean_lib «MyApp» where
  roots := #[`MyApp.Solution]
  globs := #[.submodules `MyApp]
  precompileModules := true

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target]
target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())
```

A program adds a `lean_exe` whose root is a WorldCode module; then `main` must reach every hole.
`Challenge` stays out of the default targets, since its holes share names with the solution's
definitions. Add `/comparator.json` to `.gitignore`: the build writes it from `Challenge.lean`.

A module's role comes from its name: the first component that is `CoreSpec`, `WorldSpec`,
`CoreCode`, or `WorldCode`. Any other module, like `MyApp.Solution`, is tooling.

- CoreSpec and CoreCode are pure: no `partial`, `unsafe`, `@[extern]`, `@[implemented_by]`,
  initializers, IO, or `dbg*`. CoreCode imports only CoreSpec and CoreCode.
- WorldSpec holds `@[extern] opaque` declarations and world claims, and is otherwise pure.
- WorldCode may do IO and call foreign code, but not use `unsafe`, `@[extern]`, or
  `@[implemented_by]`.
- Every role uses only the standard axioms. Modules outside the package are trusted.
- Recursion is structural, well-founded, or `partial_fixpoint`. A `partial_fixpoint` hole needs a
  headline marked `@[terminates hole]` that states on which inputs it returns.

`Challenge.lean` meta-imports `SoftwareChallenge`, imports only CoreSpec and WorldSpec, and
declares each hole with the code's exact type, `def name : T := sorry`.

## Run

```sh
lake build        # audit and headline report
lake test         # your tests, including the live suites
lake comparator   # MyApp/Solution.lean proves exactly the statements in Challenge.lean
lake script run software_challenge/grade <commit>   # judge a candidate from this checkout
```

The audit reruns and prints its report only when a module or an owned file changes; `.lake/build/softwareChallenge.txt` keeps the last report.

The report's `Edit:` line lists the files agents change, and its `Owned:` line the files that
decide what is claimed. A build fails when an owned file differs from `owned.lock`; delete the
lock to record a new statement. `grade` refuses a
candidate that changes or adds an owned file, then builds it in a fresh worktree and runs `lake build`,
`lake comparator` and `lake test`; it exits 0 to accept, 1 to refuse, and 3 when it cannot
judge. `Check` on foreign code needs `precompileModules`. `lake comparator` replays the
headline proofs through the kernel in a separate process, which rejects proofs that skipped
the kernel during the build.
