module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesExchangeTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesArgumentsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesArgsStepProof
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (table argsNext row)
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowRawExchangeVerticesCodecProof (decoded)
open NumberedWindowRawExchangeVerticesArgumentsProof (argsCell)
open NumberedWindowRawExchangeVerticesExchangeTableProof
  (EarlierAgreement successfulView earlierTerm earlierArgs)

theorem argsStep (hp : HeadPairs) (a b : Nat) (inductionAt : EarlierAgreement hp a b)
    (h : (row hp a b).2 = true) : (bounds a).2 = (bounds b).2 := by
  have reported : argsNext (table hp (pair a b)) a b = true := by
    rw [successfulView hp a b (Or.inr h)] at h
    exact h
  cases a with
  | zero => simp [argsNext] at reported
  | succ i =>
    cases b with
    | zero => simp [argsNext] at reported
    | succ j =>
      cases ha : decode i with
      | none => simp [argsNext,ha] at reported
      | some pa =>
        rcases pa with ⟨headA,tailA⟩
        cases hb : decode j with
        | none => simp [argsNext,ha,hb] at reported
        | some pb =>
          rcases pb with ⟨headB,tailB⟩
          let prev := table hp (pair (i+1) (j+1))
          have choices :
              (((prev.getD (pair headA headB) (false,false)).1 = true) ∧ tailA = tailB) ∨
              (headA = headB ∧ (prev.getD (pair tailA tailB) (false,false)).2 = true) := by
            simpa [prev,argsNext,ha,hb,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] using reported
          obtain ⟨_,headALe,tailALe⟩ := decoded ha
          obtain ⟨_,headBLe,tailBLe⟩ := decoded hb
          have agreed : (bounds headA).1 = (bounds headB).1 ∧ (bounds tailA).2 = (bounds tailB).2 := by
            rcases choices with ⟨heads,tailEq⟩ | ⟨headEq,tails⟩
            · exact ⟨earlierTerm hp inductionAt (Nat.lt_succ_of_le headALe)
                (Nat.lt_succ_of_le headBLe) heads,congrArg (fun n => (bounds n).2) tailEq⟩
            · exact ⟨congrArg (fun n => (bounds n).1) headEq,
                earlierArgs hp inductionAt (Nat.lt_succ_of_le tailALe)
                  (Nat.lt_succ_of_le tailBLe) tails⟩
          rw [argsCell ha,argsCell hb,agreed.1,agreed.2]

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesArgsStepProof
