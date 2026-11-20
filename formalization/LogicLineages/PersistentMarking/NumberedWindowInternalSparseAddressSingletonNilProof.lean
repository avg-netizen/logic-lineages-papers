module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTerminalChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySeedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveIterationTerminalChecks (exact_OpenTerminalNilLoop)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)
open NumberedWindowInternalSparsePositiveOutputFinishProof (terminalValue)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (finishAtRename)

/-- Original chosen-fuel finish observes the same current at the real
zero raw-code tail. The actual scratch graph is constructed internally. -/
theorem finishNil {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty dst : OTerm α) :
    Nonempty (Derivation body Γ (finishAt raw least ctx ty dst z dst)) := by
  apply scratchCases z (suc dst) (finishAt raw least ctx ty dst z dst)
  intro β j Δ state _ pair
  rw [finishAtRename,zRelabel]
  simp only [zRelabel,sucRelabel] at pair
  let c := ctx.relabel j
  let t := ty.relabel j
  let current := suc (dst.relabel j)
  have loop := closedApply (exact_OpenTerminalNilLoop body raw least β state z c t current) pair
  exact terminalValue raw least state c t current z z current loop pair ⟨refl z⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
