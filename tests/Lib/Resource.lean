import DevWidgets.Lib

namespace DevWidgets.Tests.Lib.Resource

private def assertEq [BEq α] [ToString α] (label : String) (expected actual : α) : IO Unit := do
  unless expected == actual do
    throw <| IO.userError s!"{label}: expected {expected}, got {actual}"

#eval show IO Unit from do
  let events ← IO.mkRef (#[] : Array String)
  let n : Nat ← DevWidgets.Lib.withResource
    (do
      events.modify (·.push "acquire")
      pure 7)
    (fun r failed =>
      events.modify (·.push s!"release:{r}:{failed}"))
    (fun r => do
      events.modify (·.push s!"use:{r}")
      pure (r + 1))
  assertEq "withResource result" 8 n
  assertEq "withResource events" #["acquire", "use:7", "release:7:false"] (← events.get)

#eval show IO Unit from do
  let events ← IO.mkRef (#[] : Array String)
  let didFail ←
    try
      let n : Nat ← DevWidgets.Lib.withResource
        (do
          events.modify (·.push "acquire")
          pure 3)
        (fun _ failed =>
          events.modify (·.push s!"release:{failed}"))
        (fun _ => do
          events.modify (·.push "use")
          throw <| IO.userError "boom")
      let _ := n
      pure false
    catch _ =>
      pure true
  unless didFail do
    throw <| IO.userError "expected `withResource` test body to fail"
  assertEq "withResource failure events" #["acquire", "use", "release:true"] (← events.get)

#eval show IO Unit from do
  let released ← IO.mkRef false
  let n : Nat ← DevWidgets.Lib.withResourceUnit
    (pure 11)
    (fun _ => released.set true)
    (fun x => pure (x + 1))
  assertEq "withResourceUnit result" 12 n
  assertEq "withResourceUnit release-called" true (← released.get)

end DevWidgets.Tests.Lib.Resource
