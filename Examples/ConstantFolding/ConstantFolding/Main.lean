module

import ConstantFolding.Output

public section

def main : IO Unit := IO.println (ConstantFolding.output (.add (.lit 2) (.lit 3)))
