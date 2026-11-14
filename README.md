# Lean Software Challenge

A Lean library for software whose guarantees are machine-checked. A repository that uses it is a
challenge: its owner states what the program must do as theorems, and agents submit code and
proofs. Requires **Lean 4.35.0**.

## Concepts

- **Challenge.** `Challenge.lean`, written by the owner. It states the headlines, holes and kills
  with `sorry`.
- **Hole.** A function of the program that a headline mentions, declared in `Challenge.lean` as
  `def name : T := sorry` with the code's exact type. The solution's definition of the same name
  fills it.
- **Headline.** A theorem about the program, stated in terms of the specification, that assumes
  only world claims.
- **Kill.** `¬` a headline with its holes, and the foreign constants of WorldSpec, replaced by
  wrong ones, marked `@[kills headline]`. It shows that the headline rejects a wrong
  implementation; every headline needs one.
- **World claim.** `WorldClaim Name := P`, an assumption about foreign code: hardware, the
  operating system, a native library. Its doc comment names the observation that would falsify
  it.
- **Check.** A test of a world claim against the real foreign code: one instance that must follow
  from the claim, or an IO action that throws to fail.
- **Roles.** A module's role is the first component of its name that is `CoreSpec`, `WorldSpec`,
  `CoreCode` or `WorldCode`; any other module, such as `MyApp.Solution`, is tooling.
- **Solution.** The module named `Solution`, which proves the headlines and kills.
- **Owned files.** The files that decide what is claimed. `owned.lock` records a hash of each.
- **Report.** What every build prints: each headline with the world claims it assumes and how
  many checks each has, the headlines not yet proved, how many are proved, and the `Edit:` and
  `Owned:` lines. `.lake/build/softwareChallenge.txt` keeps it.

## What an accepted solution guarantees

- **Every headline is proved.** The kernel checked each proof, and `lake comparator` replays it.
- **The code that runs is the code proved.** CoreSpec and CoreCode are pure. Recursion is
  structural, well-founded, or a `partial_fixpoint` hole whose return a headline states. Foreign
  code enters only through `@[extern] opaque` declarations in WorldSpec, CoreCode never calls
  it, and `main` reaches every hole.
- **Every headline can fail.** Each has a kill.
- **Every assumption is named and tested.** A headline assumes only the world claims it takes as
  hypotheses, and `lake test` runs at least one check of each.
- **What is claimed did not change.** A build fails when an owned file differs from
  `owned.lock`, and `grade` refuses a candidate that edits one.

A challenge in progress builds: the report marks each headline the solution does not prove yet,
and `lake test` and `grade` refuse until all are proved.

## Files

| File | Contains | Approved by |
|---|---|---|
| `Challenge.lean` | the headlines, holes and kills, stated with `sorry` | owner |
| `MyApp/CoreSpec.lean` | the types and reference definitions the headlines are stated in | owner |
| `MyApp/WorldSpec.lean` | `@[extern] opaque` declarations, and the world claims about them | owner |
| `owned.lock` | a hash of each owned file, recorded by the first build | owner |
| `MyApp/CoreCode.lean` | the program's pure code and its proofs | agents |
| `MyApp/WorldCode.lean` | IO, calls to foreign code, `main`, and the checks | agents |
| `MyApp/Solution.lean` | the proofs of the headlines and kills | agents |

| Role | May contain | May import |
|---|---|---|
| CoreSpec, CoreCode | pure code: no `partial`, `unsafe`, `@[extern]`, `@[implemented_by]`, initializers, IO, or `dbg*` | CoreCode imports only CoreSpec and CoreCode |
| WorldSpec | `@[extern] opaque` declarations and world claims, otherwise pure | |
| WorldCode | IO and calls to foreign code, but not `unsafe`, `@[extern]`, or `@[implemented_by]` | |

Every role uses only the standard axioms, and modules outside the package are trusted.
`Challenge.lean` imports only CoreSpec and WorldSpec. A `partial_fixpoint` hole needs a headline
marked `@[terminates hole]` that states on which inputs it returns.

## Example

From the [template](Examples/ConstantFolding), where `output_correct` says the output is the true
value of an expression, assuming native addition is correct. Each file has
`meta import SoftwareChallenge`.

```lean
-- MyApp/WorldSpec.lean
/-- The adder agrees with `Nat.add`. A different sum for any pair falsifies it. -/
WorldClaim AddAgrees (add : Nat → Nat → Nat) := ∀ a b, add a b = a + b

-- MyApp/WorldCode.lean
Check AddAgrees nativeAdd : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71
Check AddAgrees nativeAdd := do
  for a in [0, 1, 2 ^ 64] do
    unless nativeAdd a 7 - a == 7 do throw (.userError s!"nativeAdd {a} 7 disagrees")

-- Challenge.lean
theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :
    output e = toString (eval (fun _ => 0) e)
@[kills output_correct] theorem output_correct_rejects_suffix :
    ¬ (AddAgrees Nat.add → ∀ e : Expr,
      (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e))
```

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

- A program adds a `lean_exe` whose root is a WorldCode module.
- `Challenge` stays out of the default targets, since its holes share names with the solution's
  definitions.
- Add `/comparator.json` to `.gitignore`: the build writes it from `Challenge.lean`.
- Commit `lean-toolchain` and `lake-manifest.json`: they pin Lean and this library's commit, and
  they are owned.

## Run

```sh
lake build        # the audit, the report, and comparator.json
lake test         # the build, lint, every check, and lake comparator
lake script run software_challenge/grade <commit>   # judge a candidate from this checkout
```

To record a new statement, delete `owned.lock` and build. `lake comparator` replays the proofs
through the kernel in a separate process, which rejects proofs that skipped the kernel during the
build. `grade` refuses a candidate that changes or adds an owned file, then runs `lake test` in a
fresh worktree of it; it exits 0 to accept, 1 to refuse, and 3 when it cannot judge.
