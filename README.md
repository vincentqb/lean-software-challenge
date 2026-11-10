# Lean Software Challenge

A repository that uses this library is a challenge: implement code that does what its headline
theorems say. You own the challenge, and agents submit solutions made of code and proofs.
Requires **Lean 4.35.0**.

## What an accepted solution guarantees

- **Its status is truthful.** ● means the kernel proved the headline; ◕ means it rests on a
  named open conjecture.
- **The code that runs is the code proved.** Spec and core code is pure, foreign code enters only
  through `@[extern] opaque` bindings, and `main` reaches every hole.
- **Every headline can fail.** A kill proves it rejects a wrong implementation.
- **Every assumption is named and tested.** A headline assumes only the world claims it takes as
  hypotheses, and each has a `Test`, `Check`, or live suite.
- **What is claimed did not change.** `grade` refuses a candidate that edits a file listed on
  the report's `Owned:` line.

## Files

| File | Contains | Approved by |
|---|---|---|
| `Challenge.lean` | the headline theorems and their kills, stated with `sorry` | you |
| `comparator.json` | the headlines, kills, and holes `lake comparator` checks | you |
| `MyApp/Spec.lean` | types, reference definitions, and the claims headlines rest on | you |
| `MyApp/Boundary.lean` | `@[extern] opaque` declarations for foreign code | you |
| `Audit.lean` | the role of each module prefix | you |
| `MyApp/Core/…` | pure code: public interface, private helpers, and their proofs | agents |
| `MyApp/Shell.lean` | IO that connects the core to the world, and `main` | agents |
| `MyApp/Solution.lean` | proofs of the headlines and kills | agents |

Headlines are end-to-end theorems: they say what the program does in terms of the spec,
assuming only named claims. In the [template](Examples/ConstantFolding), whose challenge is
[`ConstantFoldingChallenge.lean`](ConstantFoldingChallenge.lean), `output_correct` says the
shell prints the true value of an expression, assuming native addition is correct.

## Syntax

```lean
public meta import SoftwareChallenge

/-- The adder agrees with `Nat.add`. A different sum for any pair falsifies it. -/
WorldClaim AddAgrees (add : Nat → Nat → Nat) := ∀ a b, add a b = a + b
Check AddAgrees nativeAdd : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71
@[exercises AddAgrees] def nativeAddSuite : IO Unit := ...

Conjecture Normalizes (optimize : Expr → Expr) := ∀ e, normal (optimize e) = true
Test Normalizes fold : normal (fold (.add (.add (.lit 1) (.lit 2)) (.var 0))) = true := by decide

theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e)
theorem output_correct_rejects_suffix :
    ¬ (AddAgrees Nat.add → ∀ e : Expr,
      (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e))
```

- `WorldClaim Name := P` names an assumption about the world; its doc comment names the
  observation that would falsify it, and the foreign code it constrains is a parameter.
- `Check Claim : instance` runs one instance of a claim during the build, foreign code included.
- `@[exercises Claim]` marks a live suite that exercises a claim; the report names it.
- `Conjecture Name := P` names a claim not yet proved; a theorem of type `Name` listed in
  `comparator.json` proves it.
- `Test Claim : instance := proof` proves one instance of a claim in the kernel.
- A headline takes the claims it rests on as hypotheses; `lake build` reports it proved (●)
  once its conjectures are proved and derived (◕) until then.
- A kill is `¬` a headline with its holes and boundary constants replaced by wrong ones; every
  headline needs one in `comparator.json`.

Claims live in spec modules.

## Setup

In `lakefile.lean`:

```lean
require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())
```

In `Audit.lean`, the longest matching prefix gives each module its role:

```lean
module
public meta import SoftwareChallenge.Audit

public meta def main : List String → IO Unit := SoftwareChallenge.Audit.run {
  layers := #[(`MyApp, .tooling), (`MyApp.Spec, .spec), (`MyApp.Boundary, .boundary),
    (`MyApp.Core, .core), (`MyApp.Shell, .shell)] }
```

- `.spec` and `.core` code is pure: no `partial`, `unsafe`, `@[extern]`, `@[implemented_by]`,
  initializers, IO, or `dbg*`.
- `.boundary` code is `@[extern] opaque` declarations only.
- `.shell` code may do IO but not `unsafe`, `@[extern]`, or `@[implemented_by]`.
- `.tooling` covers `Solution` and scripts; like every role, it may use only standard axioms.
- Non-`meta` imports run from tooling to shell to core to spec and boundary, never back;
  other libraries must be listed in `trusted`, which defaults to `Init`, `Std`, and `Lean`.
- `entry` names the program's entry point, `main` by default, which must be declared in a
  shell module. A library, whose users call its holes directly, sets `entry := none`.

`Challenge.lean` imports only spec and boundary modules and declares each core or shell
function a headline mentions as a hole with the code's exact type, `def name : T := sorry`;
[`comparator.json`](comparator.json) lists exactly its theorems and holes. Put `Solution` in a
default target, and declare `Challenge` as a `lean_lib` that is not one, with
`leanOptions := #[⟨`warn.sorry, false⟩]`. The audit imports every module of the default
targets into one environment, so only one of them may define `main`.

## Run

```sh
lake build        # audit and headline report
lake test         # your tests, including the live suites
lake comparator   # MyApp/Solution.lean proves exactly the statements in Challenge.lean
lake script run software_challenge/grade <commit>   # judge a candidate from this checkout
```

The audit reruns and prints its report only when a module, `Audit.lean`, `comparator.json`, or
`Challenge.lean` changes; `.lake/build/softwareChallenge.txt` keeps the last report.

The report's `Owned:` line lists the files that decide what is claimed. `grade` refuses a
candidate that changes or adds one, then builds it in a fresh worktree and runs `lake build`,
`lake comparator` and `lake test`; it exits 0 to accept, 1 to refuse, and 3 when it cannot
judge. `Check` on foreign code needs `precompileModules`. `lake comparator` replays the
headline proofs through the kernel in a separate process, which rejects proofs that skipped
the kernel during the build.
