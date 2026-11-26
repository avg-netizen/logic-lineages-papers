module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericContextProof
open NumberedWindowRawContextAlgorithm (context Frame)

private theorem contextSuccess (tag : Nat) (ws : List Nat) (lhs rhs : Nat × List Nat)
    (w f child g : Nat) (tagIs : tag = 5) (rows : ws = [w]) :
    context tag ws lhs rhs = some (f,child,g) →
    child = w ∧ ∃ dom cod arg, lhs = (6,[dom,cod,f,arg]) ∧ rhs = (6,[dom,cod,g,arg]) := by
  fun_cases context tag ws lhs rhs
  case case1 => simp at tagIs
  case case2 => simp at tagIs
  case case3 => simp at tagIs
  case case4 => simp at tagIs
  case case5 => simp at tagIs
  case case6 => simp at tagIs
  case case7 => simp at tagIs
  case case8 => simp at tagIs
  case case9 w' s t q a u v r b tests =>
    intro accepted
    have wEq : w' = w := by simpa using rows
    have seen : s = u ∧ t = v ∧ a = b := by
      simpa [Bool.and_eq_true,beq_iff_eq,and_assoc] using tests
    obtain ⟨hs,ht,ha⟩ := seen
    have coords : (q,w',r) = (f,child,g) := Option.some.inj accepted
    have hf : q = f := congrArg Prod.fst coords
    have hw : w' = child := congrArg (fun a : Frame => a.2.1) coords
    have hg : r = g := congrArg (fun a : Frame => a.2.2) coords
    exact ⟨hw.symm.trans wEq,s,t,a,by rw [← hf],by rw [← hs,← ht,← hg,← ha]⟩
  case case10 =>
    intro rejected
    cases rejected
  case case11 =>
    intro rejected
    cases rejected

theorem contextFive (lhs rhs : Nat × List Nat) (w f child g : Nat)
    (accepted : context 5 [w] lhs rhs = some (f,child,g)) :
    child = w ∧ ∃ dom cod arg, lhs = (6,[dom,cod,f,arg]) ∧ rhs = (6,[dom,cod,g,arg]) :=
  contextSuccess 5 [w] lhs rhs w f child g rfl rfl accepted

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericContextProof
