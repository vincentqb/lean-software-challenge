module

public meta import SoftwareChallenge.Audit

public meta def main : List String → IO Unit := SoftwareChallenge.Audit.run {
  layers := #[(`ConstantFolding, .tooling), (`ConstantFolding.Spec, .spec),
    (`ConstantFolding.Boundary, .boundary), (`ConstantFolding.Core, .core),
    (`ConstantFolding.Shell, .shell)] }
