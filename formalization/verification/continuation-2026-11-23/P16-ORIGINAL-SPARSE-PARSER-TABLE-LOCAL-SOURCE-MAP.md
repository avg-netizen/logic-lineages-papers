# Paper 16: physical adjacency and row head in the unchanged sparse parser

This is the thin local proof stage needed by the actual original packed
multiset parser used in the arithmetic predicates
([ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex),
lines 74–98). It is not a new parser or a proof of the resulting operator.

* The source definitions are the literal `scratchBase`, `scratchStep`,
  `scratchTable` and `scratchRow` of
  [NumberedWindowInternalSparseFieldParser.lean](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseFieldParser.lean),
  unchanged; the available parameters in those ASTs are not external
  replacement declarations. Specializing B/R to the original `parserBase`
  and `parserStep` gives the exact same open reports as the actual parser.
* [Thin proof](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseParserTableLocalProof.lean):
  with two actual adjacent table reports on the same parameters, recover
  the actual successor step at its supplied preceding value, open the
  real new R output in the original calculus, and use the actual cons
  destructor to recover the previous table as the physical tail.
  From an actual row and same-index table report, recover its actual
  head-program report. No external evaluation or default row is used.
* Historical #629's open cons parser proof uses a broad generic
  `ExchangeRowMemo.TableProof` for lookup. The corresponding generic
  tail/head arguments are re-cut on these exact original parser ASTs,
  without importing its unrelated exchange/verifier/ordinal infrastructure.
  The existing lightweight `SparseFieldParserOpenTableProof` proved forward
  construction, not these two converse graph observations. This leaf does
  not yet prove repeated drop, row lookup at a true difference, full open
  parser cons or nil, per-cons U, or any numbered result.

Author status: source only; two named native axiom audits are requested.
