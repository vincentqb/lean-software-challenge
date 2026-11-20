module

public section

namespace SoftwareChallenge

def runTests (tests : Array (String × String × String × IO Unit)) : IO UInt32 := do
  let mut failed := 0
  for (place, test, claim, action) in tests do
    match ← action.toBaseIO with
    | .ok () => IO.println s!"{place}: {test} passed, testing {claim}"
    | .error error =>
      failed := failed + 1
      IO.eprintln s!"{place}: {test} failed with `{error}`, so the native code may break the world claim {claim}. \
        Fix the native code, or the test if it misstates {claim}, then run `lake test`."
  IO.println s!"Tests: {tests.size - failed} of {tests.size} passed"
  return if failed == 0 then 0 else 1

end SoftwareChallenge
