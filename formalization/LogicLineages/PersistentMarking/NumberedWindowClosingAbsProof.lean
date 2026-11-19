import LogicLineages.PersistentMarking.NumberedWindowClosingFreshProof
import LogicLineages.PersistentMarking.NumberedWindowClosingScopeProof
import LogicLineages.PersistentMarking.NumberedWindowRealizationTypingProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingAbsProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing
open NumberedWindowClosingFreshProof (Fresh FreshArgs)
open NumberedWindowClosingScopeProof (Below belowEmpty belowPush)
open NumberedWindowFrameTargets
open NameBridge (Name)

private def ScopeAt (C : Spine.BoundContext) (d : Nat) (σ : Ty) : Prop :=
  C d = some σ ∧ Below C (d+1)

private theorem push {C d σ} (h : ScopeAt C d σ) (τ : Ty) : ScopeAt (C.push τ) (d+1) σ :=
  ⟨h.1,belowPush h.2 τ⟩

private theorem boundCase (n : Name) (C : Spine.BoundContext) (d i : Nat) (τ : Ty)
    (hi : C i = some τ) (h : ScopeAt C d n.1) :
    closeAt n d (substitute (.cons (.free n.1 n.2) .nil) d (.bound τ i)) = .bound τ i := by
  by_cases hl : i < d
  · simp only [substitute,hl,if_true,closeAt]
  · have he : i = d := by
      have hi' := h.2 i τ hi
      omega
    subst i
    have hτ : τ = n.1 := Option.some.inj (hi.symm.trans h.1)
    subst τ
    simp [substitute,shift,NArgs.get,closeAt]

mutual
private theorem term (n : Name) (C : Spine.BoundContext) (d : Nat) (q : NTerm) (τ : Ty)
    (ht : Typed C q τ) (hf : Fresh n q) (hs : ScopeAt C d n.1) :
    closeAt n d (substitute (.cons (.free n.1 n.2) .nil) d q) = q := by
  cases q with
  | free σ x =>
    change (σ,x) ≠ n at hf
    simp only [substitute,closeAt,hf,if_false]
  | bound σ i =>
    cases ht with
    | bound hi => exact boundCase n C d i _ hi hs
  | lam σ q =>
    cases ht with
    | lam hq =>
      simp only [substitute,closeAt,term n _ (d+1) q _ hq hf (push hs σ)]
  | bottom σ => rfl
  | ordinary f bs =>
    cases ht with
    | ordinary hb => simp only [substitute,closeAt,bases n C d bs _ hb hf hs]
  | numbered f τ k bs es =>
    cases ht with
    | numbered hb he =>
      simp only [substitute,closeAt,bases n C d bs _ hb hf.1 hs,extras n C d es he hf.2 hs]
  | auxApp σ τ q a =>
    cases ht with
    | auxApp hq ha =>
      simp only [substitute,closeAt,term n C d q _ hq hf.1 hs,term n C d a _ ha hf.2 hs]
termination_by sizeOf q

private theorem bases (n : Name) (C : Spine.BoundContext) (d : Nat) (As : NArgs) (ds : List Ty)
    (ht : BaseTyped C As ds) (hf : FreshArgs n As) (hs : ScopeAt C d n.1) :
    closeArgsAt n d (substituteArgs (.cons (.free n.1 n.2) .nil) d As) = As := by
  cases As with
  | nil => rfl
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      simp only [substituteArgs,closeArgsAt,term n C d q _ hq hf.1 hs,bases n C d qs _ hqs hf.2 hs]
termination_by sizeOf As

private theorem extras (n : Name) (C : Spine.BoundContext) (d : Nat) (As : NArgs)
    (ht : ExtrasTyped C As) (hf : FreshArgs n As) (hs : ScopeAt C d n.1) :
    closeArgsAt n d (substituteArgs (.cons (.free n.1 n.2) .nil) d As) = As := by
  cases As with
  | nil => rfl
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      simp only [substituteArgs,closeArgsAt,term n C d q _ hq hf.1 hs,extras n C d qs hqs hf.2 hs]
termination_by sizeOf As
end

theorem absBody : ClosingRecoversAbsBody := by
  intro σ x τ body n Q ht hf hr
  exact term (σ,x) (Spine.EmptyContext.push σ) 0 Q τ
    (NumberedWindowRealizationTypingProof.typed hr _ _ ht)
    (NumberedWindowClosingFreshProof.realized (σ,x) hr hf) ⟨rfl,belowPush belowEmpty σ⟩

end LogicLineages.PersistentMarking.NumberedWindowClosingAbsProof
