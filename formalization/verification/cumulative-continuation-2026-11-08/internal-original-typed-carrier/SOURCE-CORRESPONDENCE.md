# Original canonical typed carrier: frozen supporting specification

This packet is a supporting prerequisite for paper06 lem:id1, not a promotion
of a numbered claim. The original source is
../06-godel-t-termination-ordering/paper.tex: lines 537–549 describe well-typed
auxiliary syntax and function-side application reduction; lines 551–556 specify
the type-preserving primary equivalence and least-code representatives.

## Original domain and exact meaning

NumberedTypedCarrier.typedCanonicalCarrierTest is unchanged. It decodes the
value with the original decodeUniverse and accepts exactly when the decoded
packed term has the requested type AND its original representativeCode equals
the input value. Thus canonicality is a required part of this carrier. Neither
the raw source universe nor packed typed syntax alone is a replacement.

InternalOriginalTypedCarrier.typedValue specializes that exact function to
fixed n, arity, symbols, S and Gamma. Its two input coordinates are
[value,type]. It retains the original decodeType on the supplied type code,
then calls the unchanged typedCanonicalCarrierTest and converts its Boolean
answer to zero or one. This is the fixed-window specialization of
OrdinaryArithmeticTypedCarrier.typedValue at any encoded original context
((symbols,S),table), with its type and value coordinates reordered explicitly.
The table does not affect typed membership. No context-carrying object code or
joint-Gamma representation is substituted for the original scalar value.

All natural value/type pairs and arbitrary finite S are covered. Failed packed
decodes, failed universe tests, mismatched outer types and noncanonical values
remain rejected. No subtype-closure premise is added. The original type decoder
is total by the checked NumberedTypeCodecTotalProof; no natural type code is
silently removed from the quantifiers. The literal Option.any definition still
retains its original failure branch rather than changing the decoder.

## Concrete Program and three exact targets

The wrapper checker is an explicit binary Program AST. It conjoins, with the
existing exact-one InternalAcceptance.conjunction:

1. The shared InternalOriginalStepGuard.Data.sourceValid leaf at value.
2. The original InternalUnpair.left(value) equals the supplied type code,
   checked by the existing InternalEqualityTest AST through same.
3. The supplied old typed Program at the same [value,type] coordinates.

The same unary sourceValid Program is already used by the original step and
structural endpoint wrappers, including for the endpoint argument. The packed
target-validity Program is not substituted for it. No correctness or internal
derivability field is added to Data. The old typed leaf is not discarded even
though its acceptance externally entails the first two guards.

ActualOriginalTypedProgramExists selects one actual binary old typed Program
for each fixed original signature/window/Gamma, before quantifying every
natural input. Primitive recursiveness of the original typed carrier and type
decoder may establish this external selection. It is not an internal rule.

ActualOriginalTypedWrapperCalibration states equality to the entire original
typedValue function on every input, given the separate all-input calibrations
of the shared validity leaves and old typed Program. A proof must show that
original typed acceptance entails the raw-universe test and numeric outer-type
equality. Decode soundness identifies the raw packed type number, and original
type-code bijectivity identifies the supplied type code. Rejected inputs still
return zero because the old exact-one typed conjunct rejects. No typed-input
restriction or hypothesis asserting the desired guard is added.

ActualOriginalTypedAcceptanceEquation is a genuine internal derivation for
arbitrary Program leaves, body, free-variable type and symbolic value/type
terms. Acceptance is equivalent to the actual shared source-validity graph,
the actual InternalUnpair.left graph with the supplied type as output, and the
old typed Program's output-one graph. In particular, no independent outer-tag
witness is required. Graph totality, functionality, composition, exact-one
conjunction and equality acceptance can prove this equation from the explicit
AST. Semantic calibration and natural evaluation truth do not supply internal
graphs. The reverse implication is also required.

## Intended use and remaining boundary

At a canonical function value x and symbolic arrow code, the internal equation
supplies the outer-tag graph of x. An accepted compatible original quotient
edge supplies sourceValid(s) and the actual wrapped source-representative graph
with output x. The already checked InternalRepresentativeTag transport can
then carry that outer-tag graph back to the raw source s. At a typed argument
a and symbolic domain code, the new equation directly supplies sourceValid(a)
and the original left(a)=domain graph. These are compatible prerequisites for
the frozen structural endpoint equation, not a completed bridge in this packet.

Further assembly must use the same concrete wrapped ASTs; equality of natural
evaluations does not identify internal graphs of different Programs. This
packet does not prove application representative congruence, application
validity transport, result-type membership evidence, the whole typed-edge rule
or CertifiedApplicationLift. It is fixed-Gamma, not a uniform joint-context
package, and does not settle malformed outer pathValue behavior. Multiset,
constructor, lambda, fundamental and closed all-term ID1 claims remain pending.

## Freeze status

Definitions, Targets, Preflight and this correspondence are frozen before
proof authorship. Independent specification review and successful native
preflight are required before proof authorship. No compiler has run for this
packet and no compiler slot has been acquired. No existing frozen source,
register, resource setting or Git state is changed. Standard-axiom and bounded
serialized compiler acceptance remain required; no full-root or remote-CI
result is claimed.
