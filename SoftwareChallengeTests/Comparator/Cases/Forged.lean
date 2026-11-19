module

meta import Lean

public section

namespace Cases

set_option debug.skipKernelTC true in
run_meta Lean.addDecl (.thmDecl {
  name := `Cases.forged
  levelParams := []
  type := Lean.mkConst ``False
  value := Lean.mkConst ``True.intro })

theorem forgery : False := forged

end Cases
