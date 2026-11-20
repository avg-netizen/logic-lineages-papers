module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTransportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)

theorem moveSource {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty early late code target : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn early late)))
    (known : Nonempty (Derivation body Γ (positiveAt raw least ctx ty early code target))) :
    Nonempty (Derivation body Γ (positiveAt raw least ctx ty late code target)) := by
  apply graphInputTransport body α 5 Γ (OrdinaryArithmetic.graphFormula (positive raw least)) (suc z)
    (args5 ctx ty early code target) (args5 ctx ty late code target) _ known
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl ctx⟩ (Fin.cases ⟨refl ty⟩ (Fin.cases eq
    (Fin.cases ⟨refl code⟩ (Fin.cases ⟨refl target⟩ (fun u => Fin.elim0 u))))) i

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTransportProof
