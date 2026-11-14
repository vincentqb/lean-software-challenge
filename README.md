# Lean Software Challenge

This library checks that a Lean program does what its owner states it must. You write the
statements; agents write the code and the proofs. Every build reports which statements are proved
about the code that runs, and on which assumptions. Requires **Lean 4.35.0**.

## What you write

You write the statement of the challenge, then review only changes to it.

- `Challenge.lean`: the headlines, theorems about the program stated with `sorry`; a hole,
  `def name : T := sorry`, for each function a headline mentions; and for each headline a kill,
  `¬` the headline with its holes replaced by a wrong implementation, marked `@[kills headline]`.
- `MyApp/CoreSpec.lean`: the types and reference definitions the headlines are stated in.
- `MyApp/WorldSpec.lean`: each foreign function the program calls, as an `@[extern] opaque`
  declaration, and a `WorldClaim` for each assumption about one. A world claim's doc comment
  names the observation that would falsify it.
- `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`, as in [Setup](#setup).

The first build records a hash of each of these files in `owned.lock`. After that, a build fails
if one of them changes. To record a new statement, delete `owned.lock` and build.

## What agents write

Agents write everything else:

- `MyApp/CoreCode.lean`: pure code, and lemmas about it.
- `MyApp/WorldCode.lean`: IO, calls to foreign functions, `main`, and at least one `Check` of
  each world claim a headline assumes.
- `MyApp/Solution.lean`: the proofs of the headlines and kills.

Holes are defined in CoreCode or WorldCode. Once the statements exist, the code and the proofs
can progress independently, headline by headline. A headline that is not proved yet stays out of
`Solution.lean`: the build passes and the report marks it. A `sorry` anywhere fails the build.

## What you get

When `lake test` passes, or `grade` accepts a candidate:

- Every headline is proved, and `lake comparator` replays each proof through the kernel.
- The proofs are about the code that runs. CoreSpec and CoreCode are pure and total, foreign code
  enters only through WorldSpec, CoreCode never calls it, and `main` reaches every hole.
- Every headline rejects a wrong implementation: each kill is proved.
- Every headline assumes only the world claims it takes as hypotheses, and a `Check` tested each
  of them against the real foreign code.
- The statement did not change: no owned file differs from `owned.lock`.

No check decides whether a headline says what its name says, or whether a `Check` exercises its
claim. You judge both.

Every build prints the report:

```
fold_preserves_meaning
fold_idempotent  (not yet proved)
output_correct  assumes AddAgrees (2 checks)
Proved: 2 of 3 headlines
Edit: ConstantFolding/CoreCode.lean ConstantFolding/WorldCode.lean ConstantFolding/Solution.lean
Owned: lakefile.lean lake-manifest.json lean-toolchain owned.lock Challenge.lean ...
```

The [template](Examples/ConstantFolding) is a complete challenge.

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

A program adds a `lean_exe` whose root is a WorldCode module. `Challenge` stays out of the
default targets because its holes share names with the solution's definitions. Commit
`lean-toolchain` and `lake-manifest.json`, and add `/comparator.json` to `.gitignore`: the build
writes it from `Challenge.lean`.

A module's role is the first component of its name that is `CoreSpec`, `WorldSpec`, `CoreCode`,
or `WorldCode`; any other module is tooling. Modules outside the package are trusted, and every
module uses only the standard axioms.

| Role | May contain | May import |
|---|---|---|
| CoreSpec, CoreCode | pure code: no `partial`, `unsafe`, `@[extern]`, `@[implemented_by]`, initializers, IO, or `dbg*` | CoreSpec; CoreCode also CoreCode |
| WorldSpec | `@[extern] opaque` declarations and world claims, otherwise pure code | CoreSpec, WorldSpec |
| WorldCode | IO and calls to foreign functions, but not `unsafe`, `@[extern]`, or `@[implemented_by]` | anything but tooling |
| tooling | anything | anything |

`Challenge.lean` imports CoreSpec, WorldSpec, and `SoftwareChallenge`. A `partial_fixpoint` hole
needs a headline marked `@[terminates hole]` that states on which inputs it returns.

## Run

```sh
lake build        # audit, report, and comparator.json
lake test         # build, lint, every Check, and lake comparator
lake script run software_challenge/grade <commit>   # judge a candidate from this checkout
```

`grade` refuses a candidate that changes or adds an owned file, then runs `lake test` in a fresh
worktree of it. It exits 0 to accept, 1 to refuse, and 3 when it cannot judge.
