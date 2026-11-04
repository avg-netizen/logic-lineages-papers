module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceBetaInstanceDownwardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceBetaInstanceDownwardTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedQuotientPaths

def ActualBetaInstanceDownward : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (sigma tau : Ty) (body body' : AuxTerm (Fin n) arity (sigma::Gamma) tau)
      (a : AuxTerm (Fin n) arity Gamma sigma),
    InUniverse ctx.1.1 ctx.1.2 body → InUniverse ctx.1.1 ctx.1.2 body' → InUniverse ctx.1.1 ctx.1.2 a →
    PositivePath (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (sigma::Gamma))
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,body⟩) (representativeCode ctx.1.1 ctx.1.2 ⟨tau,body'⟩) →
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute body (singleSubstitution a)⟩) →
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute body' (singleSubstitution a)⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceBetaInstanceDownwardTargets
