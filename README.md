# Lean Software Challenge

This library checks that a Lean program does what its owner states it must. You write the
statements; agents write the code and the proofs. `lake lint` reports which statements are proved
about the code that runs, and on which assumptions. Requires **Lean 4.35.0**.

## What you write

You write the statement of the challenge, then review only changes to it.

- `Challenge.lean`: the headlines, theorems about the program stated with `sorry`; a hole,
  `def name : T := sorry`, for each function a headline mentions; and for each headline a kill,
  `¬` the headline with its holes, and any WorldSpec foreign functions, replaced by wrong
  implementations, marked `@[kills headline]`.
- `MyApp/CoreSpec.lean`: the types and reference definitions the headlines are stated in.
- `MyApp/WorldSpec.lean`: each foreign function the program calls, as an `@[extern] opaque`
  declaration, and a `WorldClaim` for each assumption about one. A world claim's doc comment
  names the observation that would falsify it.
- `MyApp/Solution.lean` containing only `module`, which agents fill in.
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

Once exactly one module is named `Solution`, `lake build` records a hash of each of these files but
`Solution.lean`, and of every other module whose role is CoreSpec or WorldSpec, in `owned.lock` when
there is none. After that, `lake build` and `lake lint` fail if one of them changes. To record a new
statement, delete `owned.lock` and run `lake build`.

## What agents write

Agents write everything else:

- `MyApp/CoreCode.lean`: pure code, and lemmas about it.
- `MyApp/WorldCode.lean`: IO, calls to foreign functions, `main`, and at least one `Check` of
  each world claim a headline assumes.
- `MyApp/Solution.lean`: the proofs of the headlines, kills, and witnesses. It has
  `meta import SoftwareChallenge`, whose linter records which world claims each proof uses.

Holes are defined in CoreCode or WorldCode. Once the statements exist, the code and the proofs
can progress independently, headline by headline. A headline that is not proved yet stays out of
`Solution.lean`: `lake build` and `lake test` pass, `lake lint` exits 2 and lists it under Pending,
and `lake comparator` and `lake exe grade` refuse until it is proved. A `sorry` anywhere fails
`lake lint`.

## What you get

Each step adds checks the steps before it do not make, and runs none of them; Lake reuses their
builds.

When `lake build` passes, the code compiles, exactly one module is named `Solution`, and the
statement is well formed: every headline has
a kill, every precondition that mentions a hole or a foreign function has a witness, no two
headlines state the same up to binder names, every hole is mentioned, and every hypothesis of a
headline that mentions no input is a world claim. No owned file differs from `owned.lock`. It
writes `comparator.json` from `Challenge.lean`.

When `lake lint` exits 0, Lean's linters pass, and:

- Every headline, kill, and witness is proved in `Solution` or a module it imports, with the
  statement `Challenge.lean` gives it, up to binder names and binder kinds, as `lake comparator`
  compares them. Each hole is a `def` of the type `Challenge.lean` gives it.
- The proofs are about the code that runs. CoreSpec and CoreCode are pure and total, except a
  `partial_fixpoint` hole whose `@[terminates]` headline states where it returns; foreign code
  enters only through WorldSpec, CoreCode never calls it, and in a program `main` reaches every
  hole.
- Every headline rejects a wrong implementation: each kill is proved.
- Every headline can apply: some input meets its preconditions. Its kill shows this for
  preconditions that mention no hole or foreign function, and its proved witness for the others.
- Every world claim a headline assumes has a `Check`, and every module uses only the standard
  axioms.
- No owned file differs from `owned.lock`, and `comparator.json` matches `Challenge.lean`.

When `lake test` exits 0, every `Check` passed against the real foreign code, and so did the
package's own tests.
`lake test` runs the Checks concurrently, `SOFTWARE_CHALLENGE_JOBS` at a time (default: the
hardware threads, at most 16), and prints each Check's time, slowest first, so a Check must not
depend on another Check's order or side effects.

When `lake comparator` accepts, the kernel accepted every proof replayed from a sandboxed export,
with only the standard axioms. The build alone does not ensure this: a proof can skip the kernel
with `debug.skipKernelTC`.

When `lake exe grade <commit>` accepts, the candidate changes no owned file, and every step above
passes on it, judged by the base's copy of this library.

No check decides whether a headline says what its name says, whether it is as general as it
could be, or whether a `Check` exercises its claim. You judge those; the report helps.

`lake lint` prints the report:

```
fold_preserves_meaning
fold_idempotent  (not yet proved)
fold_normalizes  (kill not yet proved)
fold_two_plus_three  (one instance)
output_correct  assumes AddAgrees (2 checks, unused by the proof)
Proved: 4 of 5 headlines, 4 of 5 kills
Independent: 1 of 5 headlines
Unclaimed: 2 of 6 definitions main runs
  main run
Pending: 2
  Challenge.lean:34: ConstantFolding.fold_idempotent is not proved yet, so the solution does not ...
  ...
Edit: ConstantFolding/CoreCode.lean ConstantFolding/WorldCode.lean ConstantFolding/Solution.lean
Owned: lakefile.lean lake-manifest.json lean-toolchain owned.lock Challenge.lean ...
```

- `(not yet proved)`, `(kill not yet proved)`, `(witness not yet proved)`: the solution does not
  prove the headline, one of its kills, or one of its witnesses yet.
- `(stated differently)`: the solution states the headline otherwise than `Challenge.lean`.
- `(outside Solution's imports)`: a module that `Solution` does not import proves it.
- `(one instance)`: the headline quantifies over no input, so it states one case.
- `(bundles k laws)`: the headline is a conjunction, an `↔`, or a `Prop` structure of `k` laws;
  stating each as its own headline gives each its own kill and witness.
- `unused by the proof`: the proof does not use this world claim, so the headline holds
  without it; only you can drop it.
- `Independent`: how many headlines have a proved kill showing that the others do not imply
  them.
- `Unclaimed`: how many of the CoreCode and WorldCode definitions `main` runs no hole reaches, so
  no headline speaks about them; the next line names them. A library has no `main` and no line.
- `h terminates via t`: the `@[terminates h]` headline `t` states on which inputs the
  `partial_fixpoint` hole `h` returns.
- `Pending`: what is not done yet, each with its fix; all but a hidden dependency are the
  solution's to do. Errors, listed under `Errors`, are what it must not do.

The [template](Examples/ConstantFolding) is a complete challenge.

## Setup

In `lakefile.lean`:

```lean
import Lake
open Lean Lake DSL

package «my_app» where
  lintDriver := "software_challenge/lint_challenge"
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

@[default_target]
target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
```

A program adds a `lean_exe` whose root is a WorldCode module. `testDriverArgs := #["my_tests"]`
names scripts of the package that `lake test` runs after the Checks. `Challenge` stays out of the
default libraries because its holes share names with the solution's definitions. These options turn
all of Lean's linters on except `missingDocs`, which asks for doc comments, and `coreInternal`,
which is meant for Lean's own repository. Commit `lean-toolchain` and `lake-manifest.json`, and add
`/comparator.json` to `.gitignore`: `lake build` writes it from `Challenge.lean`. Require
`software_challenge` by git, or from a directory outside `/home`, `/root`, `/run`, `/tmp` and `/var`:
the comparator's sandbox hides those, so `lake lint` reports such a dependency as pending, which only
a new statement resolves. `lakefile.lean` is owned: after editing it, delete
`owned.lock` and run `lake build`.

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
lake build                 # compile, check the statement, write comparator.json
lake lint                  # Lean's linters and the audit; prints the report
lake test                  # every Check, then the package's own tests
lake comparator            # replay the proofs through the kernel in a sandbox
lake exe grade <commit>    # owner: judge a candidate from this checkout
```

`lake lint` runs Lean's linters itself, so the package does not set `builtinLint := true`, which
would run them twice. It exits 0 when the solution is complete, 2 when it has no error but
something is pending, and 1 on any error, a linter's warning included. `lake test` exits with the
worst code of its steps, so an own test's code passes through. Every message about a declaration
names its file and line; every message says why it matters, gives the fix, and the command to run
next.

`lake script run software_challenge/replay` runs `lake comparator` once for each theorem, several at
a time, and writes the time each run took, slowest first, to `.lake/build/comparator.txt`: a slow
proof shows at the top before it reaches a time limit. `SOFTWARE_CHALLENGE_JOBS` sets how many run
at a time (default: the hardware threads, at most 16). A run's time includes the comparator's
checks of the build and its export, not only the kernel's replay. It exits 1 when the comparator
rejects a theorem, and 2 when a run fails without a verdict.

`lake exe grade <commit>` checks the candidate out in a worktree under `.lake/grade/`, gives it
the base's copy of this library and the base's dependencies, and runs, once each, `lake build`,
`lake lint`, the Checks, the package's own tests, and one `lake comparator` with the
`comparator.json` the base wrote before the candidate's code ran. It exits 0 to accept; 1 to
refuse a candidate that changes an owned file, solves an older statement, or fails a step; and 3
when it cannot judge: the base is not a git checkout, has no `owned.lock`, has uncommitted changes
to an owned file, or fails its statement check; the candidate names no commit; the sandbox hides a
dependency; or a step fails before judging. The candidate's code runs unsandboxed and can change
the host and the verdict, so grade a candidate in a disposable container.

## Cite

```bibtex
@software{lean_software_challenge,
  author = {Quenneville-B{\'e}lair, Vincent},
  title  = {Lean Software Challenge},
  note   = {A judge for agent-written Lean software},
  year   = {2026},
  url    = {https://github.com/vincentqb/lean-software-challenge},
}
```

## Related work

- Dean Foster, [lean-manifests](https://github.com/deanpfoster/lean-manifests)
- Lean FRO, [Comparator](https://github.com/leanprover/comparator)
- [Palomar](https://palomar-registry.org)
- Lim et al., [Pre-QED: Environment Specifications for Agentic Verification](https://arxiv.org/abs/2611.15207)
- Anthropic, [LLMs are making formal software verification feasible at a much larger scale](https://www.anthropic.com/research/formal-verification)
- Theorem, [OSS Verify](https://github.com/theorem-labs/oss-verify-proofs)
