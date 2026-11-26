import LogicLineages.PersistentMarking.NumberedWindowClosingInventoryProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingTypedProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing
open NameBridge (Name)

theorem push {n d C D} (h : CloseCompatible n d C D) (σ : Ty) :
    CloseCompatible n (d+1) (C.push σ) (D.push σ) := by
  refine ⟨h.1,?_⟩
  intro i τ hi
  cases i with
  | zero => exact hi
  | succ i => exact h.2 i τ hi

private theorem freeCase {n d C D} (σ : Ty) (x : Nat) (h : CloseCompatible n d C D) :
    Typed D (closeAt n d (.free σ x)) σ := by
  by_cases he : (σ,x) = n
  · simp only [closeAt,he,if_true]
    exact .bound (by rw [← he] at h; exact h.1)
  · simp only [closeAt,he,if_false]
    exact .free

mutual
theorem term (n : Name) (d : Nat) (C D : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (h : Typed C q τ) (hc : CloseCompatible n d C D) : Typed D (closeAt n d q) τ := by
  cases q with
  | free σ x =>
    cases h with
    | free => exact freeCase σ x hc
  | bound σ i =>
    cases h with
    | bound hi => exact .bound (hc.2 i σ hi)
  | lam σ q =>
    cases h with
    | lam hq => exact .lam (term n (d+1) _ _ q _ hq (push hc σ))
  | bottom σ =>
    cases h with
    | bottom => exact .bottom
  | ordinary f bs =>
    cases h with
    | ordinary hb => exact .ordinary (base n d _ _ bs _ hb hc)
  | numbered f τ k bs es =>
    cases h with
    | numbered hb he => exact .numbered (base n d _ _ bs _ hb hc) (extras n d _ _ es he hc)
  | auxApp σ τ q a =>
    cases h with
    | auxApp hq ha => exact .auxApp (term n d _ _ q _ hq hc) (term n d _ _ a _ ha hc)
termination_by sizeOf q

theorem base (n : Name) (d : Nat) (C D : Spine.BoundContext) (As : NArgs) (types : List Ty)
    (h : BaseTyped C As types) (hc : CloseCompatible n d C D) :
    BaseTyped D (closeArgsAt n d As) types := by
  cases As with
  | nil =>
    cases h with
    | nil => exact .nil
  | cons q qs =>
    cases h with
    | cons hq hs =>
      exact .cons (term n d _ _ q _ hq hc) (base n d _ _ qs _ hs hc)
termination_by sizeOf As

theorem extras (n : Name) (d : Nat) (C D : Spine.BoundContext) (As : NArgs)
    (h : ExtrasTyped C As) (hc : CloseCompatible n d C D) :
    ExtrasTyped D (closeArgsAt n d As) := by
  cases As with
  | nil => exact .nil
  | cons q qs =>
    cases h with
    | cons hq hs =>
      exact .cons (term n d _ _ q _ hq hc) (extras n d _ _ qs hs hc)
termination_by sizeOf As
end

theorem admissible {S K n d C D τ q} (hc : CloseCompatible n d C D)
    (h : InWindow S K C τ q) : InWindow S K D τ (closeAt n d q) := by
  obtain ⟨_,hs,hh⟩ := NumberedWindowClosingInventoryProof.term n d q
  exact ⟨term n d C D q τ h.1 hc,fun t hp => h.2.1 t (hs ▸ hp),
    fun f hf => h.2.2 f (hh ▸ hf)⟩

end LogicLineages.PersistentMarking.NumberedWindowClosingTypedProof
