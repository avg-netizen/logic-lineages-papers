module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakeningTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax
open NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceComputabilityFormula SourceFirstOrderWeakening

def ActualFirstOrderComputabilityReflection : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarNew : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    ∀ sigma : Ty,
    Calibrates scalarOld context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    Calibrates scalarNew context (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) →
    ∀ tau : Ty, FirstOrder tau → ∀ q : AuxTerm (Fin n) arity Gamma tau,
    InUniverse ctx.1.1 ctx.1.2 q →
    Computable n arity (sigma :: Gamma) (fun x => x ∈ leastSet scalarNew context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,rename q (Renaming.weaken Gamma sigma)⟩) →
    Computable n arity Gamma (fun x => x ∈ leastSet scalarOld context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakeningTargets
