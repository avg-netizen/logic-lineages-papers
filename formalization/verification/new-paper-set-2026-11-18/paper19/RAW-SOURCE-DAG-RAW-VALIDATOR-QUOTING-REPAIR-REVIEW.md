# Independent proposed parser repair

Inspected the new unfrozen RawValidator definitions and all current proof-local references. The declaration `def variable` and its expression references use a reserved Lean keyword. Approve only lexical escaping to `«variable»` for that same identifier in the declaration, nodeValid use, and proof-local expressions/simp references. Leave `variable_primitive`, comments and all bodies/types unchanged. This is a name-quotation repair, not a new validator or relaxed bounds/arity/type rule.

The preserved failed edition is raw-source-dag-primitive-draft01, receipt 1795021383951861464-5. All six original frozen source pins remain matched; no pin update should be needed because these helpers are new and unfrozen. Require applied exact-diff confirmation before a fresh parent retry. No native execution by reviewer.
