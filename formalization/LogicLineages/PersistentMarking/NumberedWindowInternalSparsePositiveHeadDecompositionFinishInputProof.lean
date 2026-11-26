module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishInputProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph)

theorem moveInput {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (out ctx ty early late cert : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn early late)))
    (known : Nonempty (Derivation body Γ (finishGraph raw least out ctx ty early cert))) :
    Nonempty (Derivation body Γ (finishGraph raw least out ctx ty late cert)) := by
  apply graphInputTransport body α 4 Γ (OrdinaryArithmetic.graphFormula (finish raw least)) out
    (args4 ctx ty early cert) (args4 ctx ty late cert) _ known
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl ctx⟩ (Fin.cases ⟨refl ty⟩ (Fin.cases eq
    (Fin.cases ⟨refl cert⟩ (fun u => Fin.elim0 u)))) i

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishInputProof
