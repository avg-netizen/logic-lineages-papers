module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax
open NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceComputabilityFormula

/-- All simple types, with the original finite window and no added membership
condition on the erased variable's type. -/
def ActualComputabilitySingleBottom : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarNew : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    ∀ sigma : Ty,
    Calibrates scalarOld context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    Calibrates scalarNew context (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) →
    ∀ (tau : Ty) (q : AuxTerm (Fin n) arity (sigma :: Gamma) tau), InUniverse ctx.1.1 ctx.1.2 q →
    (Computable n arity (sigma :: Gamma) (fun x => x ∈ leastSet scalarNew context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩) ↔
    Computable n arity Gamma (fun x => x ∈ leastSet scalarOld context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute q (singleSubstitution (.bottom sigma))⟩))

/-- Genuine all-type weakening, with computability both preserved and reflected. -/
def ActualComputabilityWeakening : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarNew : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    ∀ sigma : Ty,
    Calibrates scalarOld context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    Calibrates scalarNew context (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) →
    ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau), InUniverse ctx.1.1 ctx.1.2 q →
    (Computable n arity Gamma (fun x => x ∈ leastSet scalarOld context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩) ↔
    Computable n arity (sigma :: Gamma) (fun x => x ∈ leastSet scalarNew context) context tau
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,rename q (Renaming.weaken Gamma sigma)⟩))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportTargets
