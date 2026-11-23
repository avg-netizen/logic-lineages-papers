# Paper 16: exact original sparse parser lookup and thin cons proof

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex),
74–98 uses arithmetic certificates on the original sparse raw numeric carrier.
These are source-local supplier stages for the actual parser in those graphs.

1. [Literal lookup](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseParserLookupProof.lean):
   for a genuine bounded subtraction report, open the actual low table value
   on the same parser parameters. #1547 exact drop produces that very code;
   #1543 exact head identifies its row; the actual original lookup graph
   composes those two observations. No change of recurrence, AST, index,
   valuation, gap or theorem premises.
2. [Thin open step](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseFieldParserThinOpenStepProof.lean):
   re-cut the checked #629 original proof script around the new literal
   lookup root. In the certified row step, its actual tail and order bound
   pay the new exact difference lookup. The remaining original cell,
   subtraction, prepend and branch proof is unchanged except namespace
   and imports. The previous broad generic ExchangeRowMemo theorem is
   not imported.
3. [Thin open cons and nil](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseFieldParserThinOpenConsProof.lean):
   re-cut the checked #629 literal cons-forward argument against that thin
   step and the existing actual raw cons, tail-order, and cell proofs.
   Nil is directly the checked original table base row passed through
   the parser's original row selector. These give the same actual
   `consFromPrepend` forward relation and literal nil parser graph; this
   stage does not claim all malformed/parser reverse cases.

No original source files changed. The blocked historical parser roots
and per-cons U edition are untouched; binding the new supplier to U
requires a separate exact reconciliation after these native gates.
No numbered promotion or resource setting changes.

Native staged roots: LookupProof (1 alias), ThinOpenStepProof (1 alias),
ThinOpenConsProof (2 aliases). Author status: source only.
