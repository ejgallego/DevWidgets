/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import DevWidgets.CE.Widget
public import DevWidgets.Lib.Commands
public meta import DevWidgets.CE.Widget
public meta import DevWidgets.CE.Analysis
public meta import Lean.Server.Rpc.RequestHandling
meta import Lean.Widget.Commands
public section

namespace DevWidgets.CE

-- Keep RPC wrappers in a module that imports the implementation for meta execution.
@[server_rpc_method]
meta def ceOptionSchema (params : CEOptionSchemaParams) :
    Lean.Server.RequestM (Lean.Server.RequestTask CEOptionSchema) :=
  ceOptionSchemaImpl params

@[server_rpc_method]
meta def irAtPos (params : IRAtPosParams) :
    Lean.Server.RequestM (Lean.Server.RequestTask IRAtPosResponse) :=
  irAtPosImpl params

end DevWidgets.CE

