module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceEvaluationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree exactEqualityEvaluation)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowInternalSparsePathEnvelope
  (run hopGood hopTarget hopSource hopWitness hopRawTarget)
open NumberedWindowInternalSparsePathAdvance

abbrev eval4 (p : Program 4) (c ty s h : Nat) : Nat :=
  evaluate p (c ::ᵥ ty ::ᵥ s ::ᵥ h ::ᵥ nil)

def sourceCode (least : Program 3) (c ty hop : Nat) :=
  evaluate least (c ::ᵥ ty ::ᵥ run hopSource hop ::ᵥ nil)

def destinationCode (least : Program 3) (c ty hop : Nat) :=
  evaluate least (c ::ᵥ ty ::ᵥ run hopRawTarget hop ::ᵥ nil)

def actualStep (raw : Program 5) (c ty hop : Nat) :=
  evaluate raw (c ::ᵥ ty ::ᵥ run hopSource hop ::ᵥ run hopWitness hop ::ᵥ run hopRawTarget hop ::ᵥ nil)

def passes (raw : Program 5) (least : Program 3) (c ty current hop : Nat) : Prop :=
  current ≠ 0 ∧ run hopGood hop = 1 ∧ actualStep raw c ty hop = 1 ∧
    sourceCode least c ty hop = current ∧ destinationCode least c ty hop = run hopTarget hop + 1

private theorem vectorFive (f : Fin 5 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ f 4 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun m =>
    Fin.cases ?_ (fun n => Fin.cases ?_ (fun u => Fin.elim0 u) n) m) l) k) i <;> simp <;> rfl

theorem hopValue (p : Program 1) (c ty s h : Nat) :
    eval4 (atHop p) c ty s h = run p h := by
  unfold eval4 atHop run
  rw [evaluate,vectorOne]
  rfl

theorem targetValue (c ty s h : Nat) :
    eval4 targetCode c ty s h = run hopTarget h + 1 := by
  unfold eval4 targetCode
  rw [evaluate,vectorOne]
  change eval4 (atHop hopTarget) c ty s h + 1 = _
  rw [hopValue]

private theorem rawValue (raw : Program 5) (c ty s h : Nat) :
    eval4 (rawCall raw) c ty s h = actualStep raw c ty h := by
  unfold eval4 rawCall actualStep
  rw [evaluate,vectorFive]
  change evaluate raw (c ::ᵥ ty ::ᵥ eval4 (atHop hopSource) c ty s h ::ᵥ
    eval4 (atHop hopWitness) c ty s h ::ᵥ eval4 (atHop hopRawTarget) c ty s h ::ᵥ nil) = _
  rw [hopValue,hopValue,hopValue]

private theorem leastValue (least : Program 3) (p : Program 1) (c ty s h : Nat) :
    eval4 (leastCall least p) c ty s h = evaluate least (c ::ᵥ ty ::ᵥ run p h ::ᵥ nil) := by
  unfold eval4 leastCall
  rw [evaluate,vectorThree]
  change evaluate least (c ::ᵥ ty ::ᵥ eval4 (atHop p) c ty s h ::ᵥ nil) = _
  rw [hopValue]

private theorem equalValue (p q : Program 4) (c ty s h : Nat) :
    eval4 (.composition equalityTest ![p,q]) c ty s h = 1 ↔
      eval4 p c ty s h = eval4 q c ty s h := by
  unfold eval4
  rw [evaluate,vectorTwo]
  change evaluate equalityTest (eval4 p c ty s h ::ᵥ eval4 q c ty s h ::ᵥ nil) = 1 ↔ _
  rw [exactEqualityEvaluation]
  split <;> simp_all

private theorem presentValue (c ty s h : Nat) :
    eval4 statePresent c ty s h = 1 ↔ s ≠ 0 := by
  unfold eval4 statePresent
  rw [evalBranch]
  change (if s = 0 then 0 else 1) = 1 ↔ _
  split <;> simp_all

private theorem andValue (p q : Program 4) (c ty s h : Nat) :
    eval4 (conjunction p q) c ty s h = 1 ↔ eval4 p c ty s h = 1 ∧ eval4 q c ty s h = 1 := by
  unfold eval4
  rw [conjunctionEvaluation]
  split <;> simp_all

theorem guardValue (raw : Program 5) (least : Program 3) (c ty s h : Nat) :
    eval4 (advanceGood raw least) c ty s h = 1 ↔ passes raw least c ty s h := by
  unfold advanceGood passes
  rw [andValue,andValue,andValue,andValue,presentValue,hopValue,rawValue]
  unfold fromMatches toMatches
  rw [equalValue,equalValue,leastValue,leastValue,targetValue] <;> rfl

theorem resultValue (raw : Program 5) (least : Program 3) (c ty s h : Nat)
    [Decidable (passes raw least c ty s h)] :
    eval4 (advance raw least) c ty s h =
      if passes raw least c ty s h then run hopTarget h + 1 else 0 := by
  have result : eval4 (advance raw least) c ty s h =
      if eval4 (advanceGood raw least) c ty s h = 0 then 0 else eval4 targetCode c ty s h := by
    unfold advance eval4
    rw [evalBranch] <;> rfl
  rw [result,targetValue]
  by_cases hyes : passes raw least c ty s h
  · rw [(guardValue raw least c ty s h).mpr hyes,if_neg (Nat.succ_ne_zero 0),if_pos hyes]
  · have zeroGuard : eval4 (advanceGood raw least) c ty s h = 0 := by
      have hno : eval4 (advanceGood raw least) c ty s h ≠ 1 := fun e =>
        hyes ((guardValue raw least c ty s h).mp e)
      unfold advanceGood eval4 at *
      rw [conjunctionEvaluation]
      rw [conjunctionEvaluation] at hno
      split <;> simp_all
    rw [zeroGuard,if_pos rfl,if_neg hyes]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceEvaluationProof
