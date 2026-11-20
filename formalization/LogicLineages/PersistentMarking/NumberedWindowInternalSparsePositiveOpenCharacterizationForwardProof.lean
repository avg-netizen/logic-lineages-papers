module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationTerminalRulesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveFold (iterateState)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs loopArgsRename moveLoop)
open NumberedWindowInternalSparsePositiveTerminalityChecks (exact_OpenChosenFuelTerminal)
open NumberedWindowInternalSparsePositiveTerminalScratchCasesProof (terminalCases)
open NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof
open NumberedWindowInternalSparsePositiveOpenCharacterizationTerminalRulesProof (recoverAtState)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem terminalForOutput (raw : Program 5) (least : Program 3) (ctx ty source cert target state : OTerm α)
    (ok : Nonempty (Derivation body Γ (acceptance raw least ctx ty source cert target)))
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty (suc source) cert))) :
    Nonempty (Derivation body Γ (certificateResult raw least ctx ty source cert target)) := by
  have done := closedApply (exact_OpenChosenFuelTerminal body raw least α state ctx ty (suc source) cert) loop
  apply terminalCases state (certificateResult raw least ctx ty source cert target) done
  intro β j Δ current hJ pair
  rw [resultRename]
  have a := renameInto ok j Δ hJ
  rw [acceptanceRename] at a
  have l := moveLoop j Δ hJ raw least state cert ctx ty (suc source) cert loop
  rw [sucRelabel] at l
  exact recoverAtState raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
    (cert.relabel j) (target.relabel j) (state.relabel j) current a l pair

theorem forward (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (ok : Nonempty (Derivation body Γ (acceptance raw least ctx ty source cert target))) :
    Nonempty (Derivation body Γ (certificateResult raw least ctx ty source cert target)) := by
  apply programCases (iterateState raw least) (loopArgs cert ctx ty (suc source) cert) _
  intro β j Δ state hJ loop
  rw [resultRename]
  rw [loopArgsRename,sucRelabel] at loop
  have a := renameInto ok j Δ hJ
  rw [acceptanceRename] at a
  exact terminalForOutput raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
    (cert.relabel j) (target.relabel j) state a loop

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationForwardProof
