# P17: original ordered signed terminal row emission

Printed source: `arithmetic.tex`, `thm:arithmetic`, the separate original
signed terminal rows of a plain Boolean formula.

* Use the original formula codec's ordered atom traversal without
  deduplication. Each original atom's decoded signed constant, ordered
  term occurrence weights (including zero and cancelled weights), and
  coordinate names are copied exactly into the typed projection's raw
  row representation. Nonnegativity and positive-modulus divisibility
  tags match the original clauses literally.
* The entire raw tape on a genuine source formula encoding is exactly
  the list of encoded typed terminal rows (and has the same atom count).
  Weight, atom and whole tape programs are primitive recursive.
* This is only exact **projection** of the already-defined typed
  terminal rows. It does not authorize a nonlinear or malformed input,
  establish semantic admission of a formula, produce the graph-row
  prefix, compile a high witness, or decide an original query.
