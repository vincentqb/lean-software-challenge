import SoftwareChallengeTests.Suite

def main (args : List String) : IO UInt32 := do
  SoftwareChallengeTests.run ((args.head?.map System.FilePath.mk).getD (← IO.currentDir))
