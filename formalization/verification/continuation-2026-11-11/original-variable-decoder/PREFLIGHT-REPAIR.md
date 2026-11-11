# Preflight syntax repair

Attempt 1, coordinator receipt `1794400330597350843-5`, failed at reserved identifier `matches` in Definitions line 18. Before repair, all three frozen specification files and the SHA manifest were preserved in `preflight-attempt1/`. The only source change renames that definition and its check-body reference to `matchesType`; the AST, four contracts and every quantifier remain unchanged. This explicit syntax correction is refrozen in the current SHA manifest. No candidate proofs have been authored.
