namespace SoftwareChallengeTests

structure Ran where
  code : UInt32
  output : String

def childEnv : Array (String × Option String) :=
  #["LEAN_PATH", "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE"].map (·, none)

def runIn (dir : System.FilePath) (cmd : String) (args : Array String) : IO Ran := do
  let out ← IO.Process.output { cmd, args, cwd := dir, env := childEnv }
  return { code := out.exitCode, output := out.stdout ++ out.stderr }

def lakeIn (dir : System.FilePath) (args : Array String) : IO Ran := do
  runIn dir ((← IO.getEnv "LAKE").getD "lake") args

def gitIn (dir : System.FilePath) (args : Array String) : IO Ran :=
  runIn dir "git" (#["-c", "user.name=lsc-test", "-c", "user.email=lsc-test@localhost", "-c", "commit.gpgsign=false",
    "-c", "init.defaultBranch=base"] ++ args)

inductive Edit where
  | replace (file old new : String)
  | write (file text : String)

def Edit.apply (dir : System.FilePath) : Edit → IO Unit
  | .replace file old new => do
    let text ← IO.FS.readFile (dir / file)
    unless text.contains old do throw (.userError s!"{file} does not contain `{old}`")
    IO.FS.writeFile (dir / file) (text.replace old new)
  | .write file text => do
    if let some parent := (dir / file).parent then IO.FS.createDirAll parent
    IO.FS.writeFile (dir / file) text

partial def copyTree (source destination : System.FilePath) : IO Unit := do
  if ← source.isDir then
    IO.FS.createDirAll destination
    for entry in ← source.readDir do
      unless [".lake", "comparator.json"].contains entry.fileName do copyTree entry.path (destination / entry.fileName)
  else IO.FS.writeBinFile destination (← IO.FS.readBinFile source)

def overrides (lsc : System.FilePath) : String :=
  s!"\{\"version\": \"1.3.0\", \"packages\": [\{\"type\": \"path\", \"scope\": \"\", \"name\": \"software_challenge\", \
    \"manifestFile\": \"lake-manifest.json\", \"inherited\": false, \"dir\": \"{lsc}\", \"copy\": false, \
    \"configFile\": \"lakefile.lean\"}]}"

def templateCopy (lsc dir : System.FilePath) (edits : List Edit) : IO Unit := do
  IO.FS.createDirAll dir
  for entry in ← dir.readDir do
    unless [".lake", ".git"].contains entry.fileName do
      if ← entry.path.isDir then IO.FS.removeDirAll entry.path else IO.FS.removeFile entry.path
  copyTree (lsc / "Examples" / "ConstantFolding") dir
  IO.FS.createDirAll (dir / ".lake")
  IO.FS.writeFile (dir / ".lake" / "package-overrides.json") (overrides lsc)
  for edit in edits do edit.apply dir

def expect (ran : Ran) (what : String) (code : UInt32) (says : List String) : Except String Unit := do
  unless ran.code == code && says.all (ran.output.contains ·) do
    throw s!"{what} exited {ran.code} and printed\n{ran.output}\nexpected exit {code} and {says}"

end SoftwareChallengeTests
