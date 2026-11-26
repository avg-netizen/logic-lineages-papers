module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityMotiveProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityGapProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (malformed)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveDeadCurrentChecks (exact_OpenMalformedFinishZero)

theorem badFinish {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source first mid : OTerm α) (goal : Formula α)
    (bad : Nonempty (Derivation body Γ (malformed first)))
    (known : Nonempty (Derivation body Γ (finishAt raw least ctx ty source first mid))) :
    Nonempty (Derivation body Γ goal) := by
  have no := closedApply (exact_OpenMalformedFinishZero body raw least α ctx ty (suc source) first) bad
  obtain ⟨e⟩ := valueUnique (finish raw least) (suc mid) z (args4 ctx ty (suc source) first) known no
  exact ⟨Derivation.explosion (sucNeZeroApply e)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityGapProof
