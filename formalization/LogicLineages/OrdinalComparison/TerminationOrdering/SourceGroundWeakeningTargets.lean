module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax
open NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceComputabilityFormula

def ActualGroundComputabilityWeakening : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarNew : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    ∀ sigma : Ty,
    Calibrates scalarOld context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    Calibrates scalarNew context (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) →
    ∀ q : AuxTerm (Fin n) arity Gamma .ground, InUniverse ctx.1.1 ctx.1.2 q →
    (Computable n arity Gamma (fun x => x ∈ leastSet scalarOld context) context .ground
      (representativeCode ctx.1.1 ctx.1.2 ⟨.ground,q⟩) ↔
    Computable n arity (sigma :: Gamma) (fun x => x ∈ leastSet scalarNew context) context .ground
      (representativeCode ctx.1.1 ctx.1.2 ⟨.ground,rename q (Renaming.weaken Gamma sigma)⟩))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningTargets
