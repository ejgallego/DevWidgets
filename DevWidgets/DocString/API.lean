/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import DevWidgets.DocString.Widget
public import DevWidgets.Lib.Commands
public meta import DevWidgets.DocString.Widget
meta import Lean.Server.Rpc.RequestHandling
import Lean.Widget.Commands

namespace DevWidgets.DocString

@[server_rpc_method]
public meta def docAtPos (params : DocAtPosParams) :
    Lean.Server.RequestM (Lean.Server.RequestTask DocAtPosResponse) :=
  docAtPosImpl params

end DevWidgets.DocString

