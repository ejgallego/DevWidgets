/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean

namespace DevWidgets.Lib

/--
Acquire a resource, run `use`, and run `release` exactly once after successful acquisition.

`release r failed` receives `failed := true` when `use r` failed.
Failure during acquisition does not call `release`. Cleanup should not throw: error
precedence follows `MonadFinally` (in `IO` and `ExceptT`, a cleanup error replaces
the action error). This helper does not mask cancellation or classify exceptions.
-/
def withResource [Monad m] [MonadFinally m]
    (acquire : m r) (release : r → Bool → m Unit) (use : r → m α) : m α := do
  let resource ← acquire
  let (result, _) ← tryFinally' (use resource) fun result? => do
    release resource result?.isNone
    pure ()
  pure result

/-- `withResource` variant whose release action ignores success/failure. -/
def withResourceUnit [Monad m] [MonadFinally m]
    (acquire : m r) (release : r → m Unit) (use : r → m α) : m α :=
  withResource acquire (fun r _ => release r) use

end DevWidgets.Lib
