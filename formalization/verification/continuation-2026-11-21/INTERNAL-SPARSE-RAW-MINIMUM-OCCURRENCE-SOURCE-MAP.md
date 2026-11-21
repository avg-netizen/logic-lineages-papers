# Paper 16: actual sparse raw minimum and its parsed occurrence

## Printed and executable scope

The manuscript's `16-persistent-marking-termination-ordering/sections/ordinals.tex`,
lines 70–77, uses finite effectively enumerable primary classes and optional least-code
representatives. This packet is one local supplier for that construction, not a proof
of class enumeration or selected least. `NumberedWindowClassAlgorithm.least` selects
`(members edge vertices seed).min?`; the physical supplied-pool minimum is a separate
consumer of a supplied ordered raw list.

The actual `NumberedWindowInternalSparseFieldParser.parser` reads the original
polynomial-coded sparse raw list and, on success, emits a successor-encoded standard
scratch list. `parserGraph out raw` names precisely `programGraph parser out ![raw]`.
The unchanged `orderedPoolMinimum` is `branch parser (constantZero 1) parsedMinimum`.
In its live branch, the actual `decodedScratch` composition takes the predecessor of
the same parser output, and `parsedMinimum` applies the physical `scratchMinimum` to
that scratch list. The independent physical scratch checker is `scratchMember`,
on the ordered tape `[scratch, selected]`, for the same standard scratch codec.
No raw input is reinterpreted as standard scratch bytes. The parser preserves
the distinction between zero (failure) and a successor of scratch zero (empty list).

## Exact target

`ExactOpenRawMinimumParsedOccurrence` quantifies over arbitrary positive body,
ordinary context, and open raw code and selected term k. Its antecedent is the
actual unchanged `orderedPoolMinimum` graph with output S k at the same raw code.
The consequent binds exactly one scratch term s and asserts the conjunction
of the actual `parserGraph (S s) raw`, the actual `scratchMinimum` graph with
output S k at s, and the actual unit `memberGraph s k`. The original raw and
selected terms enter the binder via the ordinary `Sum.inl` relabeling.
There are no external decoding, well-formedness, validity, closedness, or
successful parser hypotheses.

## Supplier route (plan, not an authored proof)

Use `optionGraphCases` for the actual parser at the original raw tape. The zero
case selects the actual constant-zero branch, contradicting successful minimum
by original graph functionality and successor/zero separation. In the successor
case, retain the actual parser graph at the same relabeled raw code.
`predecessorSuccessor` and actual composition yield `decodedScratch` at that
same successor's predecessor. The original `successorBranchElim` and
`compositionRecover` expose the physical `scratchMinimum` graph at exactly
that scratch term. The separate object `exact_OpenScratchMinimumOccurs`
supplies the unit scratch member graph on that same term and selected k.
Use actual formula renaming/substitution and existential introduction to
package that one witness. The source of the separate scratch lemma is pinned;
its fresh standalone recovery proof gate and independent review are separate
prerequisites to use it in a successor proof. It is not imported into the
target-only Lean import closure.

This proves neither an actual raw-list membership program nor an index in the
sparse encoding; numerical calibration cannot replace any object-calculus
premise. Directed-round/filter provenance, the complete selected least,
its output carrier, original raw matching, and the numbered accessibility
claim remain out of scope.
