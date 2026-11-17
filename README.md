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

To show a headline independent of the others, state its kill as `¬ H ∧ H₂ ∧ … ∧ Hₙ`: the negated
headline, then every other headline in file order, all with the same replacement. Its wrong
implementation is then close to a correct one, and it is public.

A headline's preconditions are its hypotheses that are not world claims. When one mentions a hole
or a foreign function, no kill shows that some input meets it, so state a witness that one does:
`∃` the inputs the preconditions use, in headline order, of the conjunction of the
preconditions, with the holes kept, marked `@[witness headline]`. If the headline assumes world
claims that mention no input, the witness assumes them first. The audit reads a headline with the
`Prop`-valued definitions of CoreSpec and WorldSpec unfolded, except world claims, so the
hypotheses and inputs of such a definition are the headline's.

The first `lake test` records a hash of each of these files in `owned.lock`. After that, `lake test`
fails if one of them changes. To record a new statement, delete `owned.lock` and run `lake test`.

## What agents write

Agents write everything else:

- `MyApp/CoreCode.lean`: pure code, and lemmas about it.
- `MyApp/WorldCode.lean`: IO, calls to foreign functions, `main`, and at least one `Check` of
  each world claim a headline assumes.
- `MyApp/Solution.lean`: the proofs of the headlines, kills, and witnesses. It has
  `meta import SoftwareChallenge`, whose linter records which world claims each proof uses.

Holes are defined in CoreCode or WorldCode. Once the statements exist, the code and the proofs
can progress independently, headline by headline. A headline that is not proved yet stays out of
`Solution.lean`: the build passes and the report marks it. A `sorry` anywhere fails the build.

## What you get

When `lake test` passes, or `lake exe grade` accepts a candidate:

- Every headline is proved, and `lake comparator` replays each proof through the kernel.
- The proofs are about the code that runs. CoreSpec and CoreCode are pure and total, foreign code
  enters only through WorldSpec, CoreCode never calls it, and `main` reaches every hole.
- Every headline rejects a wrong implementation: each kill is proved.
- Every headline can apply: some input meets its preconditions. Its kill shows this for
  preconditions that mention no hole or foreign function, and its proved witness for the others.
- No two headlines state the same, up to binder names.
- Every headline assumes only the world claims it takes as hypotheses, and a `Check` tested each
  of them against the real foreign code.
- The statement did not change: no owned file differs from `owned.lock`.

No check decides whether a headline says what its name says, whether it is as general as it
could be, or whether a `Check` exercises its claim. You judge those; the report helps.

`lake test` prints the report:

```
fold_preserves_meaning
fold_idempotent  (not yet proved)
fold_two_plus_three  (one instance)
output_correct  assumes AddAgrees (2 checks, unused by the proof)
Proved: 3 of 4 headlines
Independent: 1 of 4 headlines
Unclaimed: 2 of 6 definitions main runs
  main run
Edit: ConstantFolding/CoreCode.lean ConstantFolding/WorldCode.lean ConstantFolding/Solution.lean
Owned: lakefile.lean lake-manifest.json lean-toolchain owned.lock Challenge.lean ...
```

- `(not yet proved)`: the solution does not state the headline yet.
- `(witness not yet proved)`: the solution does not state the headline's witness yet.
- `(one instance)`: the headline quantifies over no input, so it states one case.
- `unused by the proof`: the proof does not use this world claim, so the headline holds
  without it; only you can drop it.
- `Independent`: how many headlines have a kill showing that the others do not imply them.
- `Unclaimed`: how many of the CoreCode and WorldCode definitions `main` runs no hole reaches, so
  no headline speaks about them; the next line names them. A library has no `main` and no line.

The [template](Examples/ConstantFolding) is a complete challenge.

## Setup

In `lakefile.lean`:

```lean
package «my_app» where
  testDriver := "software_challenge/test_challenge"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩,
    ⟨`linter.coreInternal, false⟩
  ]

require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
lean_lib «MyApp» where
  roots := #[`MyApp.Solution]
  globs := #[.submodules `MyApp]
  precompileModules := true

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]
```

A program adds a `lean_exe` whose root is a WorldCode module. `Challenge` stays out of the
default targets because its holes share names with the solution's definitions. `lake test` runs
Lean's linters, and these options turn all of them on except `missingDocs`, which asks for doc
comments, and `coreInternal`, which is meant for Lean's own repository. Commit
`lean-toolchain` and `lake-manifest.json`, and add `/comparator.json` to `.gitignore`: `lake test`
writes it from `Challenge.lean`. Require `software_challenge` by git, or from a directory outside
`/home`, `/root`, `/run`, `/tmp` and `/var`: the comparator's sandbox hides those, and `lake test`
refuses a dependency it cannot see.

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
lake test                  # agents and owner: audit, report, lint, every Check, and lake comparator
lake exe grade <commit>    # owner: judge a candidate from this checkout
```

`lake test` runs `lake comparator` once for each theorem, several at a time, and writes the time
each run took, slowest first, to `.lake/build/comparator.txt`: a slow proof shows at the top before
it reaches a time limit. `SOFTWARE_CHALLENGE_JOBS` sets how many run at a time (default: the
hardware threads, at most 16). A run's time includes the comparator's checks of the build and its
export, not only the kernel's replay.

`lake exe grade` refuses a candidate that changes or adds an owned file, then runs `lake test` in a
fresh worktree of it. It exits 0 to accept, 1 to refuse, and 3 when it cannot judge.
