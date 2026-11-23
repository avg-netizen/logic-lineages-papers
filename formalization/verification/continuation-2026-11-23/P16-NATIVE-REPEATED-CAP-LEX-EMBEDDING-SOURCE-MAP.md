# Paper 16: actual strict lexicographic preservation and distinct native cap blocks

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
499–511 defines the literal native successor, cap, zero, and (\omega).
This proof concerns the exact rank-free cap-block family of the preceding
gate, not the manuscript's separate tower/cofinality or height statement.

* [Proof](../../LogicLineages/PersistentMarking/NativeOrdinalRepeatedCapLexEmbeddingProof.lean):
  positive paths in the original actual `NativeBelow` relation compose
  into an actual strict edge by the checked confined strict transitivity.
  A pair ordered in the first coordinate uses the previous exact
  cross-block path; an equal first coordinate and increasing second
  coordinate uses the exact within-block path. The decreasing direction
  of the actual native relation is preserved, not redefined.
* Distinct ordered pairs yield distinct closed native terms: arithmetic
  lexicographic trichotomy chooses a strict pair direction, and equality
  of the images would produce a genuine self-edge. The only exclusion of
  such a self-edge is the original closed-native well-foundedness,
  pulled back from the actual #489 confined relation, by accessibility
  induction. No numeric measure, Rank import, or extra order axiom.
* The theorem is valid for an arbitrary actual closed index-type
  payload; choosing the original (Z) gives the exact earlier (Z)/(\omega)
  anchors. This is strict preservation plus injectivity, not an ordinal
  rank bound, upper calibration, Bachmann–Howard cofinality, or numbered
  height proof.

Native author status: source only; three exact named axiom audits.
