import DevWidgets.InfoTreeExplorer
import Lean

open Lean DevWidgets.InfoTreeExplorer

#eval show CoreM Unit from do
  let preview : FocusedPreview := { title := "title", path := #["contains > separator", "child"], output := "first\nsecond" }
  let encoded := toJson preview
  let .ok decoded := fromJson? (α := FocusedPreview) encoded
    | throwError "focused payload failed to decode"
  unless decoded.path == preview.path && decoded.output == preview.output do
    throwError "focused payload lost structure"
  let config := Config.bounded { maxNodes := 1000000 }
  unless config.maxNodes == 16384 do throwError "node budget was not clamped"
  let leaf : Elab.InfoTree := .hole ⟨`test⟩
  let deep := (List.range 1000).foldl (fun tree _ => .context (.parentDeclCtx `demo) tree) leaf
  let (bounded, truncated) := boundedInfoTree deep { maxNodes := 5 }
  unless truncated do throwError "expected bounded capture"
  let rec count : Elab.InfoTree → Nat
    | .context _ child => 1 + count child
    | _ => 1
  unless count bounded == 6 do throwError "node budget did not stop traversal"
