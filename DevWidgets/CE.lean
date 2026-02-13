/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import DevWidgets.CE.Widget
meta import Lean.Widget.Commands
public section

open DevWidgets.CE in
-- Enable the CE widget globally for modules importing `DevWidgets.CE`.
show_panel_widgets [clickPositionWidget]
