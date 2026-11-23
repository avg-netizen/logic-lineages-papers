# Paper 16: one conditional successor step of the actual internal J-union proof

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex),
lines 84–98 define the actual tagged multiset operator; lines 142–148 use the
origin-labelled strict split in the nested outer/inner proof.

[Exact leaf](../../LogicLineages/PersistentMarking/NumberedWindowInternalCertifiedUnionStepProof.lean):
* `unionGraph count a b u` is **not** an uninterpreted union predicate, an
  arithmetic sum, a list-permutation proposition in Lean, or an ordered
  append of the raw original codes. The actual program is
  `rawSourceCheck (observePartition count)` on `[u,a,b]`. It parses the
  actual three packed code inputs and applies literal `append` to the
  decoded scratch encodings of the two components before the supplied
  observer compares with the decoded original union code. This is the
  existing #1501–1503 graph path. `CountFit` is required on those actual
  scratch encodings; the proof does not infer any object formula from that
  external numeric premise or install the observer in a replacement checker.
* In `CertifiedOriginSplit`, the existing source calculus, current union
  code and its carrier derivation, original union certificate witness, and
  target are fixed before the local branches. This **unproved premise** must
  supply original component certificates and exact recombination on the same
  target. It eliminates for any formula, not a packaged conclusion about J.
  One or both components strictly descend; an unchanged component is
  literally the same code. Relabelling into a continuation must preserve all
  current assumptions. No derivation of this split is assumed from external
  occurrence-list or `Acc` facts.
* `HeldOuter` and `HeldInner` are proof interfaces to already-held lower
  cases alone: they are invoked only after proving an actual original odd edge.
  Left-only retains the held right J; right-only calls the inner strict case.
  If both decrease, actual certified J successor closure supplies J of the
  right child from J of the current right, then the outer strict case applies
  to the left child and the exact recombination.
* `exact_OriginalCertifiedUnionStep` proves only J of that single certified
  successor. Deriving the two quantified lower-case hypotheses from our
  checked original odd progressive induction, reconstructing the arithmetic
  origin split, supplying observer fit internally, and closing the whole union
  remain separate. No universal union, generated surrogate, or numbered result.

Native author status: source only; check the one exact named axiom audit.
