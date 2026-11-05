module

public import Lean.Widget.Commands

public section

/-- Configure exactly one instance of a widget in the current section or file.
Replaces any instances enabled by imports or earlier configuration commands.
The enclosing scope's configuration is restored when the section ends.
Use a fully-qualified widget name and a typed configuration value.
-/
macro "configure_panel_widget " widget:ident " with " config:term : command =>
  `(show_panel_widgets [-$widget, local $widget with $config])
