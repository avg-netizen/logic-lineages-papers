module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFrameTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingFreshProof
open NumberedWindowSyntax NumberedWindowClosing NumberedWindowTupleTargets
open NameBridge (Name freeOccurs freeOccursArgs)

mutual
def Fresh (n : Name) : NTerm → Prop
  | .free σ x => (σ,x) ≠ n
  | .bound _ _ | .bottom _ => True
  | .lam _ q => Fresh n q
  | .ordinary _ bs => FreshArgs n bs
  | .numbered _ _ _ bs es => FreshArgs n bs ∧ FreshArgs n es
  | .auxApp _ _ q a => Fresh n q ∧ Fresh n a
def FreshArgs (n : Name) : NArgs → Prop
  | .nil => True
  | .cons q qs => Fresh n q ∧ FreshArgs n qs
end

theorem realized (name : Name) {n q Q} (h : Realizes n q Q) :
    freeOccurs name q = false → Fresh name Q := by
  induction h using Realizes.rec (motive_2 := fun qs As _ =>
    freeOccursArgs name qs = false → FreshArgs name As) with
  | free =>
    intro hf e
    rw [← e] at hf
    simp [freeOccurs] at hf
  | bound => intro _; trivial
  | lam _ ih => exact ih
  | ordinary _ ih => exact ih
  | marked _ _ _ hb he =>
    intro hs
    have hp := Bool.or_eq_false_iff.mp hs
    exact ⟨hb hp.1,he hp.2⟩
  | nil => trivial
  | cons _ _ hq hs =>
    rename_i hFresh
    have hp := Bool.or_eq_false_iff.mp hFresh
    exact ⟨hq hp.1,hs hp.2⟩

theorem realizedArgs (n : Name) {b qs As} (h : RealizesArgs b qs As) :
    freeOccursArgs n qs = false → FreshArgs n As :=
  realized n (Realizes.ordinary (f := Head.zero) h)

mutual
theorem unchanged (n : Name) (d : Nat) (q : NTerm) (h : Fresh n q) :
    closeAt n d q = q := by
  cases q with
  | free σ x =>
    change (σ,x) ≠ n at h
    simp only [closeAt,h,if_false]
  | bound σ i => rfl
  | lam σ q => simp only [closeAt,unchanged n (d+1) q h]
  | bottom σ => rfl
  | ordinary f bs => simp only [closeAt,unchangedArgs n d bs h]
  | numbered f τ k bs es => simp only [closeAt,unchangedArgs n d bs h.1,unchangedArgs n d es h.2]
  | auxApp σ τ q a => simp only [closeAt,unchanged n d q h.1,unchanged n d a h.2]
termination_by sizeOf q

theorem unchangedArgs (n : Name) (d : Nat) (As : NArgs) (h : FreshArgs n As) :
    closeArgsAt n d As = As := by
  cases As with
  | nil => rfl
  | cons q qs =>
    simp only [closeArgsAt,unchanged n d q h.1,unchangedArgs n d qs h.2]
termination_by sizeOf As
end

end LogicLineages.PersistentMarking.NumberedWindowClosingFreshProof
