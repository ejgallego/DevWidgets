module

import Lean
meta import DevWidgets.CE.Analysis

open Lean DevWidgets.CE

namespace DevWidgets.Tests.CE.Compilation

set_option compiler.postponeCompile true

def compiledSample (n : Nat) : Nat := n + 1

-- A module can have elaborated declarations whose IR has not yet been generated.
-- CE must compile them immediately, and repeated requests must return fresh output.
#eval show CoreM Unit from do
  unless (← getEnv).header.isModule do
    throwError "expected a module environment for postponed-compilation regression"
  for viaPipeline in [true, false, true] do
    let (ir, lcnf) ← Testing.recompile ``compiledSample viaPipeline
    for (label, result) in [("IR", ir), ("LCNF", lcnf)] do
      match result with
      | .available code .recompiledForced _ =>
        unless code.toText.contains "compiledSample" do
          throwError "{label}: missing declaration in recompiled output"
      | .unavailable reason =>
        throwError "{label}: {CECodeResult.reasonLabel reason}"
      | _ => throwError "{label}: unexpected code origin"

end DevWidgets.Tests.CE.Compilation
