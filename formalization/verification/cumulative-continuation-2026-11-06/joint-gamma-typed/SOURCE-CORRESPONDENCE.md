# Joint-context type-indexed canonical carriers

Baseline: `2f447add0c9209c0400762d82e6962fa1add33e4`. Paper06
`paper.tex` lines 570–580 requires typedness in each C_tau clause and finite
first-order invariants. This component supplies a uniform arithmetic typed
carrier, not the computability predicate or its closure/induction proof.

The PR target names ORIGINAL NumberedTypedCarrier.typedCanonicalCarrierTest
with Gamma inside its ordinary input. The raw-code helper uses the accepted
rawUniverseDecode and raw representative, and is calibrated exactly back to
the original typed checker on every input. It preserves the type equality,
universe decoder, canonical representative equality and rejection behavior.

The new typedValue wrapper decodes the EXISTING ContextUniform.Object code
and calls ORIGINAL OrdinaryArithmeticTypedCarrier.typedValue using that
Gamma. Context, type and object-payload numberings are unchanged. Its encoded
predicate is the literal original predicate lifted through that decoder;
fixed fibers recover the original predicate. Malformed codes are covered.

The final target requires an actual Program 3 whose evaluation agrees with
the wrapper for EVERY vector. Its formula is the existing ordinary-arithmetic
graph compiler applied to output one, not an arbitrary formula chosen by
truth. The same formula is calibrated on all natural inputs and, for the
original subtype-closed window, exactly to a genuine original Packed term
of the stated type, universe membership and canonical representative code.
Gamma is universally quantified with the same single Program.

Nonduplication: existing OrdinaryArithmeticTypedCarrierSupportProof and
OrdinaryArithmeticTypedCarrierProof only supply PR/formulas with fixed Gamma.
Accepted ContextUniformPrimary proofs cover the untyped canonical carrier,
not its type-indexed test. JointGammaPrograms/Semantics cover untyped scalar,
list, positive and direct predicates. No accepted joint-Gamma typed carrier
or actual typed object-code formula was found.

New definitions/targets and original semantic hashes are frozen before proof
creation. Preflight, exact aliases, source-matched receipts and standard-axiom
audits use unchanged serialized caps. No existing target/source, manuscript,
register, checker, dependency, root import or CI change. Uniform application,
C_tau assembly/closure and internal ID1 proof trees remain further work.
No II5, accessibility, well-foundedness or whole lem:id1 claim.
