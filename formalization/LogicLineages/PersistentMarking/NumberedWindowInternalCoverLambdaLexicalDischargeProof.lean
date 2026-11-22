module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalDischargeProof
open NumberedWindowLexicalAlgorithm (Requirement empty slot join restrict discharge binder holds)
open NumberedWindowInternalCoverLambdaLexicalSourceTargets

private theorem restrictHolds (C : Nat → Option Nat) (b : Bool) (r : Requirement) :
    holds C (restrict b r) = (b && holds C r) := by
  simp only [holds,restrict,Bool.and_assoc]

private theorem joinSlot (C : Nat → Option Nat) (i t : Nat) (r : Requirement) :
    holds C (join (slot i t) r) = ((C i == some t) && holds C r) := by
  simp [holds,join,slot,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

private theorem indexZero (g : List Nat) (dom t : Nat) :
    ((dom::g)[0]? == some t) = (t == dom) := by
  by_cases e : t = dom
  · subst t
    simp
  · have e' : dom ≠ t := Ne.symm e
    simp [e,e']

private theorem dischargeHolds (g : List Nat) (dom : Nat) (slots : List (Nat × Nat)) :
    holds (fun i => g[i]?) (discharge dom slots) =
      slots.all (fun p => (dom::g)[p.1]? == some p.2) := by
  induction slots with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i,t⟩ := p
    cases i with
    | zero => simp only [discharge,restrictHolds,ih,List.all_cons,indexZero]
    | succ i => simp only [discharge,joinSlot,ih,List.all_cons,List.getElem?_cons_succ]

theorem exact_CoverRawLexicalBinder : ExactCoverRawLexicalBinder := by
  intro g dom r
  rw [binder,restrictHolds,dischargeHolds]
  rfl

#print axioms exact_CoverRawLexicalBinder

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalDischargeProof
