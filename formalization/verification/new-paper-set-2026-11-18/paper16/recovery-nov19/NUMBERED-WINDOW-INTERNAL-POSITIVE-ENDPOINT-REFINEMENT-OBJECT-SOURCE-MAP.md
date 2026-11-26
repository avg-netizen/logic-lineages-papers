# Open endpoint carriers of the literal positive wrapper

Target freeze only. Paper 16 `ordinals.tex` lines 65–96 use the quotient's
positive path relation with literal arithmetic certificates and actual
typedness in the positive accessibility operator. This is supporting
object-calculus evidence for those carrier formulas, not the primary
external accessibility theorem, an accessibility proof for every term,
or a typed/kinded original argument classifier.

Immutable `withEndpointCarriers i r` is exactly
`bothOne r (bothOne (atSource i) (atTarget i))`; #692 already checks that
this physical wrapper preserves original **numerical** positive checking
on all raw source/certificate/target numbers under old numerical
calibration, using #691. Neither numerical result is a premise of the
object derivation or a way to reflect open truth.

1. `ExactOpenPositiveEndpointCarrierGraphs` starts with an actual
   `Derivation B Γ` witnessing output **one** of the literal wrapper under
   arbitrary arithmetic body, hypotheses, and open terms `x,w,y`.
   Rewrite only the two genuine `bothOne` constructors to their existing
   object `InternalAcceptance.conjunction` ASTs (#619); use
   `conjunctionRecover` at each. Actual source-slot projection 0 and
   target-slot projection 2 give genuine `compositionRecover` back to
   the very same scalar `i` on `x` and `y`. The old `r` still sees the
   same ordered `[x,w,y]`. Preserve source and target as the original
   open term values, and retain the supplied witness even if not closed.
   The resulting conjunction is derived under the original premise's
   same body and hypotheses, without assuming those carrier formulas.
2. `ExactOriginalPositiveCertificateEndpointCarriers` is the actual
   original certificate formula for `S = data i j (withEndpointCarriers i r) d`
   at its actual **new** `sourceBody S c`, on the scalar slice `false`.
   The original `CheckerCoordinates.suppliedCertificate` composes
   projections **1,3,2** from the actual outer tape `[c,x,y,w]`; recover
   the chosen wrapper's genuine inner `[x,w,y]` graph with
   `compositionRecover`. Adapt both actual returned `i` graphs through
   the original `domain i` projection 1 from `[c,x]` and `[c,y]`,
   using the real checker formula's substitution equation. Return both
   actual `carrier S false c` derivations and the original `r` graph
   on the same terms, still at the **new** body. Do not transfer a proof
   from, or into, an old instantiated body. The earlier #682 certificate
   bridge is an exact syntactic construction template; it is not a
   theorem for this physically different source body.

No construction of a new selected tuple, no positive transitivity or
same-body bidirectional equivalence, no application-output carrier,
no lexical context/type identification, and no aux-free (I) or neutral
(C) result. This target requires a genuine actual open derivation,
not arbitrary external numerical equality. Target and subsequent proof
gates use the unchanged Mathlib profile 2048 heap/1536 RSS/2048 min-free,
90 CPU/180 wall/one thread, serialized by coordinator.
