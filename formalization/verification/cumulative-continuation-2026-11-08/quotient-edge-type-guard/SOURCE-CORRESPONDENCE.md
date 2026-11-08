# Original quotient-edge type guard: specification correspondence

This four-target packet is a supporting prerequisite for paper 06, `lem:id1`.
It is not the full original quotient-edge invariant package, representative
application congruence, certified application lifting, joint-context dispatch,
or the complete arithmetic accessibility theorem. Definitions and exact
comparators are frozen before proof authorship. Review and native preflight
are still required, and no proof or compiler has been started by this worker.

## Literal source contract

The paper fixes a finite subtype-closed type window at lines 537–549 of
`06-godel-t-termination-ordering/paper.tex`. Least-code representatives and
quotient edges occur at lines 551–556. The original numeric edge checker is
`NumberedNumericQuotientEdge.numericEdgeTest` with its unchanged certificate
selectors and original vertices. No source or certificate codec is replaced.

The checker decodes the certificate's raw source through `decodeUniverse`
and its raw target through `decodePackedNumber`, without adding a target
universe decoder. Each representative retains its original zero default for
a failed decode. The selected `InternalQuotientEdgeChecker.Data` stores only
the three actual Program leaves. Its original core AST remains a literal
subexpression of this wrapper, and its all-input calibration is unchanged.

The selected binary typed Program must be calibrated on every natural
`[value,type]` pair to `InternalOriginalTypedCarrier.typedValue`. This is the
original canonical typed carrier, including representative equality and all
rejection behavior, not merely raw validity with an equal type field.

## Concrete wrapper

All wrapper inputs are `[canonicalSource,canonicalTarget,certificate]`.
Its shared type is `Nat.unpair canonicalSource |>.1`. The two selected typed
calls therefore have inputs `[canonicalSource,left(canonicalSource)]` and
`[canonicalTarget,left(canonicalSource)]`. They do not read the raw source
inside the certificate, use the target's independent tag, or select a new
semantic witness.

The AST is exact-one conjunction of:

1. the literal original quotient-edge checker;
2. the selected typed Program on the source at the source endpoint's tag;
3. that SAME selected typed Program on the target at the SAME tag.

The target typed guard is additional computation outside the original core.
Its redundancy on accepted edges must be proved under subtype closure. This
packet claims no calibration for this wrapper on non-subtype-closed windows.
A later existential selection may retain old edge programs for bad windows;
no such global dispatch is silently assumed here.

## Four exact targets

1. Every accepted original numeric edge in a subtype-closed window has both
   canonical endpoints accepted by the original typedValue at the source
   endpoint's outer tag. This theorem concerns the unchanged numeric checker,
   not a newly defined guarded relation. It assumes no endpoint typing.
2. For any all-input-calibrated core data and any all-input-calibrated selected
   typed Program, the concrete wrapper agrees with the original numeric edge
   checker on ALL natural triples under subtype closure. In particular,
   rejected/malformed inputs and the original certificate zero are included.
3. From an actual arithmetic graph `graph1 InternalUnpair.left typ source`,
   wrapper acceptance is internally equivalent to original core acceptance
   and BOTH selected typed graph calls at that same symbolic `typ`.
4. Wrapper acceptance plus the actual source-tag graph internally exposes
   both selected typed predicates, especially the target one, without a
   target-typing assumption or any external semantic reflection rule.

The last two targets hold for arbitrary finite Program leaves, arbitrary
positive predicate bodies and arbitrary symbolic endpoint, certificate and
type terms. They require no calibration or subtype-closure premise. An
externally calibrated selected typed Program alone does not give an internal
source-tag theorem; a future consumer must obtain that ACTUAL graph from its
selected typed wrapper, or another internal derivation.

## Existing semantic suppliers and proof route

`NumberedNumericQuotientEdgeProof.numericQuotientEdge` extracts original
same-type packed terms q and r, source universe membership, their actual
original step, and both representative endpoint equations. That theorem
uses `NumberedNumericStepProof.numericStepCertificates` and the original
numeric decoders. `NumberedWindowReductionProof.stepGood` then derives
target universe membership using the subtype-closure hypothesis.

`NumberedTypedCarrierProof.typedCanonicalCarrier` makes each representative
accepted at their common original type. The checked
`InternalRepresentativeTagEvaluationProof.actualOriginalRepresentativeOuterType`
identifies the source representative's outer tag with the numeric code of
that common type. Original numeric type round-trip supplies the typedValue
form. These are semantic calibration suppliers, not internal inference rules.

External wrapper calibration can then use the original core calibration and
exact-one conjunction evaluation, splitting on the original Boolean output.
When the original core rejects, the wrapper still returns zero regardless
of the selected typed leaves. When it accepts, target 1 supplies both guards.
No step soundness premise is added to the final target.

The internal equations instead use the actual composition, conjunction and
unpair graph theorems. Their source-tag witness is a graph in the original
arithmetic language. External evaluation equality is never reflected into
an internal derivation on symbolic terms.

## Boundaries and later use

The selected typed Program is intentionally arbitrary subject only to the
external all-input calibration in target 2. A later chosen typed AST may
therefore expose an additional normalizer fixed-point guard, if its separate
all-input redundancy theorem is proved. This packet does not assume or prove
that normalizer theorem. The literal original typed predicate is preserved.

No full-context invariant, vertex or joint-context checker dispatch, outer
malformed-object behavior, representative fold, application congruence,
certified lift, or full source computability result is completed here. No
numbered source statement changes status. All existing frozen files and
accepted source bytes remain untouched. No Git or publication action occurs.
