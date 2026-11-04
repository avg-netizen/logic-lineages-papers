module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility
open NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative

def ActualConditionalArrowLeast : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
      (a : AuxTerm (Fin n) arity Gamma sigma),
    InUniverse ctx.1.1 ctx.1.2 f → InUniverse ctx.1.1 ctx.1.2 a →
    (∀ z : Nat, SourceComputabilityFormula.Computable n arity Gamma
      (fun y => y ∈ leastSet scalar context) context tau z → z ∈ leastSet scalar context) →
    SourceComputabilityFormula.Computable n arity Gamma (fun y => y ∈ leastSet scalar context)
      context (.arrow sigma tau) (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩) →
    SourceComputabilityFormula.Computable n arity Gamma (fun y => y ∈ leastSet scalar context)
      context sigma (representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩) →
    representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩ ∈ leastSet scalar context

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastTargets
