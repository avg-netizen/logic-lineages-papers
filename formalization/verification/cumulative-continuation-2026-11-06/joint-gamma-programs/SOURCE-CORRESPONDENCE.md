# Original encoded context-object checker programs

Baseline: `4a0b99b0ccf7c58158779a1a57faa3a084245e82`, preserving the accepted
joint-Gamma original quotient-path and direct-multiset components. Paper06
`paper.tex` lines 538–569 requires arithmetic R and DM(R) relations and typed
carrier predicates in a single tagged positive arithmetic definition. This
component constructs the missing primitive-recursive checker presentation
uniformly across encoded ambient contexts, including binder extensions.

## Exact scope and codes

The four new PR targets name ORIGINAL `ContextUniform.scalarValue`,
`listValue`, `positiveValue`, and `directValue` directly. Inputs are the original
vectors of two or four natural numbers. OrdinaryArithmeticQuotient.Context
codes and ContextUniform.Object = List Ty × Nat codes remain unchanged.
All natural inputs are covered, including malformed context/object/list or
certificate codes. Unary failures return zero. Binary checks retain exact
source/target context equality and return zero for cross-context pairs.
Original canonical-carrier, list-carrier, positive-path and direct-multiset
checks and their empty-case behavior are preserved.

The fifth comparator is the EXISTING unchanged
`ContextUniformTargets.ActualContextUniformPresentationExists`, via its
existing preflight comparator. It requires actual `SourcePresentation.Data`
with two Program 2 and two Program 4 values whose evaluations agree with the
four original functions on EVERY input. The accepted
GorbowPRProgram allPrimitiveFunctions representation theorem supplies these finite program
objects from the four PR proofs. No opaque oracle, added axiom, semantic
satisfaction surrogate or caller calibration premise is introduced.

## Nonduplication and provenance

The accepted SourcePresentationSupportProof supplies only fixed-Gamma program
families. ContextUniformTargets contains the genuinely joint-context target
but no accepted proof. The Nov 4 R005 archived ContextUniformObjectDecoderProof
and ContextUniformCheckerPrimitiveProof are unaccepted drafts. Their decoder
and composition structure may be reused transparently, but they are not
accepted suppliers. The new proof uses the now-accepted ORIGINAL joint-Gamma
positive-path and direct-multiset checker theorems, not substitute checkers.

The new targets/preflight and hashes of the original semantics and presentation
target are frozen before proof creation. Acceptance requires preflight,
exact aliases and standard-axiom audits under unchanged serialized caps.
No original file, manuscript, global register, checker, dependency, root import
or CI change. No accessibility, well-foundedness, internal ID1 derivability,
whole lem:id1 completion, or private II5 conclusion is claimed.
