import LogicLineages.PersistentMarking.NumberedWindowFrameTargets

namespace LogicLineages.PersistentMarking.NumberedWindowClosingRealizationProof
open NumberedWindowSyntax NumberedWindowClosing NumberedWindowTupleTargets
open NameBridge (Name)

private theorem freeCase (budget : Nat) (name : Name) (d : Nat) (σ : Ty) (x : Nat) :
    Realizes budget (Spine.freeSub (StructuralContext.closingMap name) d (.free σ x))
      (closeAt name d (.free σ x)) := by
  by_cases h : (σ,x) = name
  · simp only [Spine.freeSub,StructuralContext.closingMap,closeAt,h,if_true,
      Spine.shift,Nat.not_lt_zero,if_false,Nat.zero_add]
    exact .bound
  · simp only [Spine.freeSub,StructuralContext.closingMap,closeAt,h,if_false,Spine.shift]
    exact .free

theorem term (name : Name) {n q Q} (h : Realizes n q Q) :
    ∀ d, Realizes n (Spine.freeSub (StructuralContext.closingMap name) d q) (closeAt name d Q) := by
  induction h using Realizes.rec (motive_2 := fun qs As _ =>
    ∀ d, RealizesArgs n (Spine.freeSubArgs (StructuralContext.closingMap name) d qs) (closeArgsAt name d As)) with
  | free => intro d; exact freeCase n name d _ _
  | bound => intro d; exact .bound
  | lam _ ih => intro d; exact .lam (ih (d+1))
  | ordinary _ ih => intro d; exact .ordinary (ih d)
  | marked hk _ _ hb he => intro d; exact .marked hk (hb d) (he d)
  | nil => exact .nil
  | cons _ _ hq hs => rename_i depth; exact .cons (hq depth) (hs depth)

end LogicLineages.PersistentMarking.NumberedWindowClosingRealizationProof
