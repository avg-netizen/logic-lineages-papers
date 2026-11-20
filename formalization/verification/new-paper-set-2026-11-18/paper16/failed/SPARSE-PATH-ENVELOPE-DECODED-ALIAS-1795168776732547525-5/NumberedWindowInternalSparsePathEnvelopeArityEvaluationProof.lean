module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo zeroTestEvaluation exactEqualityEvaluation)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalSparseFieldCell (chosenCell cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
open NumberedWindowFieldAlgorithm (pack unpack unpackNode)

theorem applyValue (p q : Program 1) (n : Nat) :
    run (applyUnary p q) n = run p (run q n) := by
  unfold run applyUnary
  rw [evaluate, vectorOne]

theorem bothAccept (p q : Program 1) (n : Nat) :
    run (conjunction p q) n = 1 ↔ run p n = 1 ∧ run q n = 1 := by
  unfold run
  rw [conjunctionEvaluation]
  split <;> simp_all

private theorem equalValue (p q : Program 1) (n : Nat) :
    run (.composition equalityTest ![p,q]) n = 1 ↔ run p n = run q n := by
  unfold run
  rw [evaluate,vectorTwo]
  change evaluate equalityTest (evaluate p (n ::ᵥ nil) ::ᵥ evaluate q (n ::ᵥ nil) ::ᵥ nil) = 1 ↔ _
  rw [exactEqualityEvaluation]
  split <;> simp_all

theorem oneValue (n : Nat) : run one n = 1 := rfl
theorem twoValue (n : Nat) : run two n = 2 := by
  unfold two
  rw [applyValue,oneValue]
  rfl

private theorem zeroAccept (n : Nat) :
    run GorbowPRInternalControl.zeroTest n = 1 ↔ n = 0 := by
  unfold run
  rw [zeroTestEvaluation]
  split <;> simp_all

theorem bodyArity (arity n : Nat) :
    run (exactBody arity) n = 1 ↔ ∃ xs, unpack n = some xs ∧ xs.length = arity := by
  induction arity generalizing n with
  | zero =>
    rw [exactBody,zeroAccept]
    constructor
    · rintro rfl
      exact ⟨[],emptyUnpack,rfl⟩
    · rintro ⟨xs,hx,length⟩
      cases xs with
      | nil => exact packOfUnpack n hx
      | cons x ys => simp at length
  | succ k ih =>
    rw [exactBody,bothAccept,applyValue]
    cases found : chosenCell n with
    | none =>
      constructor
      · exact fun h => False.elim (noFlagOfNone found h.1)
      · rintro ⟨xs,hx,length⟩
        have bad : False := by
          by_cases nilCode : n = 0
          · subst n
            rw [emptyUnpack] at hx
            cases hx
            simp at length
          · rw [missingUnpack nilCode found] at hx
            cases hx
        exact False.elim bad
    | some pair =>
      obtain ⟨h,t⟩ := pair
      rw [(headTailOfCell found).2,ih,splitUnpack found]
      constructor
      · rintro ⟨_,xs,hx,length⟩
        refine ⟨h::xs, ?_, ?_⟩
        · rw [hx]; rfl
        · simp [length]
      · rintro ⟨xs,hx,length⟩
        refine ⟨flagOfCell found, ?_⟩
        cases tail : unpack t with
        | none => rw [tail] at hx; cases hx
        | some ys =>
          rw [tail] at hx
          have eq : h::ys = xs := Option.some.inj hx
          have succLength : (h::ys).length = k+1 := by rw [eq]; exact length
          exact ⟨ys,rfl,Nat.succ.inj succLength⟩

theorem nodeArity (tag : Program 1) (arity n k : Nat) (tagValue : run tag n = k) :
    run (nodeGood tag arity) n = 1 ↔
      ∃ xs, unpackNode n = some (k,xs) ∧ xs.length = arity := by
  unfold nodeGood
  rw [bothAccept,bothAccept,equalValue,applyValue,tagValue]
  cases found : chosenCell n with
  | none =>
    rw [noNode found]
    constructor
    · exact fun h => False.elim (noFlagOfNone found h.1)
    · rintro ⟨_,bad,_⟩
      cases bad
  | some pair =>
    obtain ⟨head,tail⟩ := pair
    obtain ⟨vh,vt⟩ := headTailOfCell found
    rw [vh,vt,bodyArity,nodeOfCell found]
    constructor
    · rintro ⟨_,same,xs,hx,len⟩
      refine ⟨xs, ?_,len⟩
      rw [hx,same]
      rfl
    · rintro ⟨xs,hx,len⟩
      cases ht : unpack tail with
      | none => rw [ht] at hx; cases hx
      | some fs =>
        rw [ht] at hx
        have eq : (head,fs) = (k,xs) := Option.some.inj hx
        have body : fs = xs := congrArg Prod.snd eq
        exact ⟨flagOfCell found,congrArg Prod.fst eq,fs,rfl,by rw [body]; exact len⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
