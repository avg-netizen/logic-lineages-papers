# Paper 16: actual internal fold on positively parsed original raw codes

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
149–153 needs an induction that covers an arbitrary accepted raw list code,
not merely an externally supplied finite list. #621's genuine sparse
induction is derived from the original internal ordered course-of-values
rule and retains the actual raw code and strictly smaller tail. This
packet uses **that same checked underlying order rule**, with a stronger
motive that tracks the actual observed scratch value as a separate binder.

* [Syntax](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseParsedFoldSyntaxProof.lean):
  the new first-order motive at raw index n is
  `∀ s (parser(n)=succ(s) → Θ(n,s))`.
  Θ may be any existing full-language formula, including the inductive
  predicate. Its two selected object arguments (raw, scratch) and prior
  free parameters are explicitly substituted and renamed. This is not an
  externally evaluated membership predicate.
* [Proof](../../LogicLineages/PersistentMarking/NumberedWindowInternalSparseParsedFoldProof.lean):
  use the original `strongInduction` that proves #621 on the same original
  arithmetic strict order, and use #1568 actual positive partition for
  progress. The nil callback receives exact raw and scratch zero proofs.
  The genuine cons branch retains its certified cell, raw cons equality,
  true strict tail bound, actual positive tail parser and exact scratch
  cons. Strictness applies the internal lower formula to the same tail;
  its own observed scratch parser graph yields the actual Θ-tail derivation
  supplied to the cons callback. Malformed codes cannot enter the positive
  partition. The result is an object universal proof and an actual instance
  at a supplied raw/scratch pair, with no host list or external Acc.
* No nil/cons Θ derivations are manufactured by this stage. In particular
  actual scratch member transport, original same-body nil J, genuine
  per-cons U and the conditional J union remain separate for the specific
  J motive. No symbolic J fold, scalar singleton closure, or numbered
  promotion is claimed.

Author status: source only; two named native axiom audits.
