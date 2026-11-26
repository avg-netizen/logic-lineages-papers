# P17: original graph protected names and first hidden candidate

Printed source: `arithmetic.tex`, `thm:arithmetic`, preservation of the
original graph variables while allocating exact untouched auxiliary names.

* Copy each original gate output and the actual ordered original input
  names. Affine inputs retain all literal term occurrences; other supported
  typed gates use their actual singleton source. Preserve whole gate-output
  tape followed by flattened references, without reordering or deduping.
* For the original Boolean terminal formula codec, use the exact original
  variables tape, plus all explicitly known names. Then take the maximum
  over all gate names. The second original base-only maximum is applied
  literally to the exact tag-filtered original base sublist before adding
  one. No replacement of the typed nested max by an unchecked
  simplification.
* Name/ref and base-filter calibration is exact on genuine source gate
  codes; the initial result is literally the original protected first
  hidden candidate for genuine known/formula/gate data. Programs are
  primitive recursive.
* This computes the initial candidate only. It does not emit any graph
  rows or make claims about an arbitrary malformed raw gate, topology,
  subsequent gate dispatch, or original query decision.
