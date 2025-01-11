import LeanAStarTest.Tests

def main (params : List String) : IO UInt32 := do
  if !params.isEmpty then
    IO.println "Currently LeanAStarTest will run all tests, and not accept parameters."
    return ⟨UInt32.size-1,by decide⟩
  let mut result : UInt32 := 0
  for (testName, test) in LeanAStarTests.ListTests do
    if let Except.error e := test () then
      IO.println s!"{testName} failed: {e}"
      result := result + 1
    else
      IO.println s!"{testName} succeeded."
  return result
