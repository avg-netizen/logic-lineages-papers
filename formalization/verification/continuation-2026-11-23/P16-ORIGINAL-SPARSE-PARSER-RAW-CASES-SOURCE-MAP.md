# Paper 16: genuine arbitrary raw sparse parser cases

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
74–98 uses the original sparse arithmetic carrier. #621's true sparse
field induction has separate nil, malformed gap and genuine cons steps.
These modules expose that exact distinction on the original parser.

* [Thin malformed leaf](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseFieldParserThinMalformedProof.lean):
  the original #629 rejection argument uses actual malformed evidence,
  including nonzero, and the real cell failure. The same parser step is
  recut against the certified thin #1551 root. It yields parser output
  zero on the original malformed code, not a fallback definition.
* [Arbitrary raw cases](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseParserRawCasesProof.lean):
  the original object calculus splits zero/successor, then actual selected
  cell results on the nonzero branch. Zero uses #1552's exact nil parser
  report (success with empty scratch). A rejected nonzero gives the actual
  malformed formula and exact zero parser output. An accepted cell opens
  real original head and tail graphs and the actual certified cell,
  establishes the genuine cons graph and literal raw term equality, and
  supplies the exact strict raw-tail order. Context preservation follows
  each actual witness and never changes the term/valuation.
* The cons branch is only a shape case: its raw tail can still be malformed.
  Positive-parent reverse success was separately checked at a given literal
  cons (#1558); lifting that result to arbitrary positive raw codes and
  any general symbolic J fold remain separate. No standard numeric
  reflection, altered parser, unconditional J, or numbered promotion.

Native staged roots: ThinMalformedProof (gap), SparseParserRawCasesProof
(exact_OriginalSparseParserRawCases). Author status: source only.
