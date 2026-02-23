/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.DocString
public section

namespace DevWidgets.DocString

/-- Response format tag for elaborated Markdown docstrings. -/
def markdownDocFormat : String := "markdown"

/-- Response format tag for raw Markdown doc-comment previews. -/
def markdownPreviewDocFormat : String := "markdown-preview"

/-- Markdown docstrings are passed to the client renderer unchanged. -/
def renderMarkdownDoc (doc : String) : String := doc

end DevWidgets.DocString
