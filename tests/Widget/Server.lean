import DevWidgets.CE
import DevWidgets.DocString
import DevWidgets.InfoTreeExplorer
import DevWidgets.PTracker

-- Imports ensure that every module used by the server fixtures has been built.
-- Lake supplies the Lean executable and search path inherited by the child server.
#eval show IO Unit from do
  let out ← IO.Process.output { cmd := "node", args := #["tests/Widget/server.mjs"] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"Widget server regression failed:\n{out.stderr}\n{out.stdout}"
