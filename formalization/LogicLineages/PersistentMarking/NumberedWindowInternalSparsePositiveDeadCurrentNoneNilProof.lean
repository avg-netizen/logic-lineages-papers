module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentGapChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneNilProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveIterationTerminalChecks (exact_OpenTerminalNilLoop)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)
open NumberedWindowInternalSparsePositiveOutputFinishProof (terminalValue)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph finishRename)

theorem nilZero {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty : OTerm α) :
    Nonempty (Derivation body Γ (finishGraph raw least z ctx ty z z)) := by
  apply scratchCases z z (finishGraph raw least z ctx ty z z)
  intro β j Δ state _ pair
  rw [finishRename]
  simp only [zRelabel] at pair ⊢
  have loop := closedApply (exact_OpenTerminalNilLoop body raw least β state z (ctx.relabel j) (ty.relabel j) z) pair
  exact terminalValue raw least state (ctx.relabel j) (ty.relabel j) z z z z loop pair ⟨refl z⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneNilProof
