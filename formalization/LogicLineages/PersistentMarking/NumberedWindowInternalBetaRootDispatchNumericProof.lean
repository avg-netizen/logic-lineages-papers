module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchNumericProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (atSlot tape)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation compositeTwo)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot)
open NumberedWindowRootDispatchAlgorithm (Rules check fixed parts)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalBetaSub (run2)
open NumberedWindowInternalBetaRootDispatch

private theorem unaryOne (w : Nat) :
    run (nodeGood (literal 1 6) 0) w = 1 ↔ unpackNode w = some (6,[]) := by
  rw [nodeArity (literal 1 6) 0 w 6 (literalEvaluation 1 6 (w ::ᵥ nil))]
  constructor
  · rintro ⟨xs,h,len⟩
    cases xs with
    | nil => exact h
    | cons x tail => simp at len
  · intro h
    exact ⟨[],h,rfl⟩

private theorem unaryBit (w : Nat) :
    run (nodeGood (literal 1 6) 0) w = 0 ∨ run (nodeGood (literal 1 6) 0) w = 1 := by
  unfold run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

attribute [local irreducible] run nodeGood literal

private theorem slotValue (q w r : Nat) :
    evaluate witnessTest (tape q w r) = run (nodeGood (literal 1 6) 0) w := by
  have coordinate : (tape q w r).get (1 : Fin 3) = w := rfl
  unfold witnessTest
  rw [atSlot,coordinate]

theorem witnessOne (q w r : Nat) :
    evaluate witnessTest (tape q w r) = 1 ↔ unpackNode w = some (6,[]) := by
  rw [slotValue]
  exact unaryOne w

private theorem witnessZero (q w r : Nat) (h : unpackNode w ≠ some (6,[])) :
    evaluate witnessTest (tape q w r) = 0 := by
  rw [slotValue]
  have seen : run (nodeGood (literal 1 6) 0) w ≠ 1 :=
    fun hit => h ((unaryOne w).mp hit)
  exact (unaryBit w).resolve_right seen

theorem callValue (beta : Program 2) (q w r : Nat) :
    evaluate (betaCall beta) (tape q w r) = run2 beta q r := by
  change evaluate (.composition beta
    (Fin.cons (.projection (0 : Fin 3)) (Fin.cons (.projection (2 : Fin 3)) Fin.elim0)))
    (tape q w r) = run2 beta q r
  rw [compositeTwo]
  rfl

/-- Conservativity for all old dispatch tables, with the beta leaf calibrated
to the table's own beta function. Non-beta cases read the unchanged old AST. -/
theorem exactOriginal (rules : Rules) (original : Program 3) (beta : Program 2)
    (oldFit : ActualRoot (check rules) original)
    (betaFit : ∀ q r, run2 beta q r = (rules.beta q r).toNat) :
    ActualRoot (check rules) (root' original beta) := by
  intro q w r
  change evaluate (root' original beta) (tape q w r) = _
  rw [root',evalBranch]
  by_cases h : unpackNode w = some (6,[])
  · have bit := (witnessOne q w r).2 h
    rw [bit,if_neg (by decide : (1 : Nat) ≠ 0),callValue,betaFit]
    rw [check,h,Option.any_some]
    rfl
  · have bit := witnessZero q w r h
    rw [bit,if_pos rfl]
    exact oldFit q w r

#print axioms exactOriginal
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchNumericProof
