module

public import SoftwareChallenge.CoreCode.Grade
public import SoftwareChallenge.CoreCode.Format

public section

namespace SoftwareChallenge.Steps.Comparator

open Lean

def run (lake : String) (dir configFile : System.FilePath) (config : Config) : IO IO.Process.Output := do
  let attempt : IO IO.Process.Output := do
    IO.FS.writeFile configFile (Config.render config)
    IO.Process.output
      { cmd := lake, args := #["comparator", "--config", configFile.toString], cwd := some dir }
  let mut output ← attempt
  for _ in [0:3] do
    unless Comparator.retryable output.exitCode (output.stdout ++ output.stderr) do break
    IO.sleep 20000
    output ← attempt
  return output

def reason : Comparator.Rejection → String
  | .kernel => "Lean's kernel rejected a proof or a declaration it uses, though the build accepted it, as \
      `debug.skipKernelTC` or `Lean.addDecl` allows"
  | .statement => "the solution states a theorem otherwise than the challenge"
  | .kind => "the solution declares a constant of the challenge as another kind of constant"
  | .absent => "the solution does not declare a theorem or hole that the challenge states"
  | .unexported => "the solution's export lacks a constant that its proofs use"
  | .differs => "the solution defines a constant otherwise than the challenge"
  | .notDefinition => "the solution declares a hole as something other than a definition"
  | .notTheorem => "the solution declares a theorem of the challenge as something other than a theorem"
  | .axiomUsed => "a proof uses an axiom beyond propext, Classical.choice, and Quot.sound"
  | .missing name => s!"the solution does not declare {name}, which the challenge states"

def remedy (solution : Name) : Comparator.Rejection → String
  | .kernel => "Prove it without `debug.skipKernelTC` or `Lean.addDecl`"
  | .statement => "State it exactly as the challenge does"
  | .kind => "Declare it as the challenge does"
  | .absent => s!"Prove it in {solution} or a module it imports"
  | .unexported => s!"Declare that constant in {solution} or a module it imports"
  | .differs => "Define it as the challenge does"
  | .notDefinition => "Declare it as a `def`"
  | .notTheorem => "Declare it as a `theorem`"
  | .axiomUsed => "Prove it without that axiom"
  | .missing name => s!"Prove {name} in {solution} or a module it imports"

def failure (output : IO.Process.Output) : String :=
  let lines := ((output.stdout ++ output.stderr).splitOn "\n").filter fun line =>
    line.startsWith "error:" || line.startsWith "bwrap:" || line.startsWith "PANIC"
  (lines.getLast?.map (·.trimAscii.toString)).getD s!"exit {output.exitCode}"

end SoftwareChallenge.Steps.Comparator
