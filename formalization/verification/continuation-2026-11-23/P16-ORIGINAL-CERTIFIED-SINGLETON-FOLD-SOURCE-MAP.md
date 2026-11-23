# Paper 16: finite proof builder on the original raw cons list

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
lines 149–153 take finite union of actual singleton J members, including the
single-scalar induction step for proper descendants.

[Proof](../../LogicLineages/PersistentMarking/NumberedWindowInternalCertifiedSingletonFoldProof.lean):
* `packedBody` uses the exact raw sparse constructor `rawCons` and literal zero.
  The input is a supplied finite ordered list of original object-language
  terms. The recursive `ConsUnionReports` stores one same-body real #1531
  `unionGraph` report at each literal singleton/actual suffix/cons join;
  occurrences and duplicates are never normalised or counted away.
* `exact_OriginalFinitePackedJ` builds a finite derivation in that same
  original body from supplied J(0), each literal singleton J, the actual
  fitted observer and per-cons reports, and #1531's two explicit arithmetic
  suppliers. The base is the supplied actual J(0) and each cons node applies
  the conditional J union; no J of a cons output is input.
* `exact_OriginalCertifiedScalarDescendantFold` requires an original even
  positive certificate at each supplied occurrence, from the same original
  scalar source. Those certify the exact original edges used with #1533's
  actual lower scalar invariant. This yields only the packed target of the
  supplied exact finite list and report spine, not a certificate decoder.
* Host recursion builds a finite object-calculus derivation on the supplied
  list. It does not quantify over arbitrary length *inside* the object
  theory. #621 sparse field induction, malformed-code rejection, actual
  reverse parser/head-tail occurrence transport, construction of open U
  reports, and genuinely same-body nil remain needed for the general proof.
  In particular, no standard scratch list is substituted for the actual
  sparse target code, no open numerical-fit reflection, no unconditional
  singleton/finite multiset closure or numbered result is asserted.

Native author status: source only; proof root expects two named axiom audits.
