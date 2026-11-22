module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (exactEqualityEvaluation vectorTwo)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation evalBranch)
open NumberedWindowFieldAlgorithm (pack unpack)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt flagOfCell headTailOfCell)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder binary)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo)
open NumberedWindowInternalCoverLexicalSlotTargets

private theorem stepPacked (k c : Nat) (g : List Nat) :
    evaluate dropStep (k ::ᵥ pack g ::ᵥ c ::ᵥ nil) = pack g.tail := by
  rw [dropStep,evalBranch]
  change (if pack g = 0 then 0 else run cellTail (pack g)) = _
  cases g with
  | nil => rfl
  | cons x xs =>
    have pos : pack (x :: xs) ≠ 0 := Nat.succ_ne_zero _
    rw [if_neg pos]
    exact (headTailOfCell (cellAt x (pack xs))).2

private theorem successorDrop (i : Nat) (g : List Nat) : (g.drop i).tail = g.drop (i+1) := by
  induction i generalizing g with
  | zero => cases g <;> rfl
  | succ i ih =>
    cases g with
    | nil => simp
    | cons x t => exact ih t

theorem exact_CoverPhysicalContextDrop : ExactCoverPhysicalContextDrop := by
  intro i
  induction i with
  | zero => intro g; rfl
  | succ i ih =>
    intro g
    change evaluate (.recursion (.projection 0) dropStep) (Nat.succ i ::ᵥ pack g ::ᵥ nil) = _
    rw [GorbowPRProgram.Proof.recursionSuccessor]
    change evaluate dropStep (i ::ᵥ evaluate dropContext (i ::ᵥ pack g ::ᵥ nil) ::ᵥ pack g ::ᵥ nil) = _
    rw [ih,stepPacked,successorDrop]

private theorem suffixFor (i : Nat) (g : List Nat) (ty : Nat) (atI : g[i]? = some ty) :
    ∃ tail, g.drop i = ty :: tail := by
  induction i generalizing g with
  | zero =>
    cases g with
    | nil => simp at atI
    | cons h t =>
      have same : h = ty := Option.some.inj atI
      exact ⟨t,by rw [same]; rfl⟩
  | succ i ih =>
    cases g with
    | nil => simp at atI
    | cons h t =>
      have here : t[i]? = some ty := atI
      obtain ⟨rest,shape⟩ := ih t here
      exact ⟨rest,shape⟩

theorem exact_CoverPhysicalLexicalSlot : ExactCoverPhysicalLexicalSlot := by
  intro g i ty atI
  obtain ⟨rest,atRest⟩ := suffixFor i g ty atI
  let xs := i ::ᵥ pack g ::ᵥ ty ::ᵥ nil
  have dropReport : evaluate dropped xs = pack (ty :: rest) := by
    change evaluate dropContext (i ::ᵥ pack g ::ᵥ nil) = _
    rw [exact_CoverPhysicalContextDrop i g,atRest]
  have live : run cellGood (pack (ty :: rest)) = 1 := flagOfCell (cellAt ty (pack rest))
  have first : run cellHead (pack (ty :: rest)) = ty := (headTailOfCell (cellAt ty (pack rest))).1
  have liveReport : evaluate inhabited xs = 1 := by
    change run cellGood (evaluate dropped xs) = 1
    rw [dropReport,live]
  have testReport : evaluate (binary equalityTest atType (.projection 2)) xs = 1 := by
    unfold binary
    rw [compositeTwo]
    change evaluate equalityTest (run cellHead (evaluate dropped xs) ::ᵥ ty ::ᵥ nil) = 1
    rw [dropReport,first,exactEqualityEvaluation,if_pos rfl]
  change evaluate slotCheck xs = 1
  rw [slotCheck,actualConjunctionEvaluation,liveReport,testReport] <;> rfl

#print axioms exact_CoverPhysicalContextDrop
#print axioms exact_CoverPhysicalLexicalSlot

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotNumericProof
