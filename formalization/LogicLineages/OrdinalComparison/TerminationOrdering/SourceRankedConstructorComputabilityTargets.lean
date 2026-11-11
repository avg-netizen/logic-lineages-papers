module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier
open PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula RankedPrecedenceCertificate

/-- The zero-numbered target with its same calibration and computable-member
hypotheses, extended to every finite label under the original rank certificate. -/
def ActualNumberedConstructorComputable : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context : Nat)
    (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
    ∀ (k : Nat) (f : Head (Fin n)) (tau : Ty)
      (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types),
    InUniverse ctx.1.1 ctx.1.2 (.numbered k f tau base types extras) →
    (∀ p ∈ argumentList base ++ argumentList extras,
      Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context p.1
        (representativeCode ctx.1.1 ctx.1.2 p)) →
    Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.numbered k f tau base types extras⟩)

/-- The ordinary, omega-label companion at the identical calibrated tuple. -/
def ActualOrdinaryConstructorComputable : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context : Nat)
    (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (rank : Fin n → Fin n), rankCertificateTest ctx.2 rank = true →
    ∀ (f : Head (Fin n))
      (base : AuxArguments (Fin n) arity Gamma (headArguments arity f)),
    InUniverse ctx.1.1 ctx.1.2 (.ordinary f base) →
    (∀ p ∈ argumentList base,
      Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context p.1
        (representativeCode ctx.1.1 ctx.1.2 p)) →
    Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context (headResult f)
      (representativeCode ctx.1.1 ctx.1.2 ⟨headResult f,.ordinary f base⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityTargets
