module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFrameTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingScopeProof
open NumberedWindowSyntax NumberedWindowDomain

def Below (C : Spine.BoundContext) (d : Nat) : Prop :=
  ∀ i τ, C i = some τ → i < d

theorem belowEmpty : Below Spine.EmptyContext 0 := by
  intro i τ h
  cases h

theorem belowPush {C d} (h : Below C d) (σ : Ty) : Below (C.push σ) (d+1) := by
  intro i τ hi
  cases i with
  | zero => omega
  | succ i => exact Nat.succ_lt_succ (h i τ hi)

mutual
theorem shiftTerm (C : Spine.BoundContext) (q : NTerm) (τ : Ty) (amount d : Nat)
    (h : Typed C q τ) (hc : Below C d) : shift amount d q = q := by
  cases q with
  | free σ x => rfl
  | bound σ i =>
    cases h with
    | bound hi => simp only [shift,hc i _ hi,if_true]
  | lam σ q =>
    cases h with
    | lam hq => simp only [shift,shiftTerm _ q _ amount (d+1) hq (belowPush hc σ)]
  | bottom σ => rfl
  | ordinary f bs =>
    cases h with
    | ordinary hb => simp only [shift,shiftBases _ bs _ amount d hb hc]
  | numbered f τ k bs es =>
    cases h with
    | numbered hb he => simp only [shift,shiftBases _ bs _ amount d hb hc,shiftExtras _ es amount d he hc]
  | auxApp σ τ q a =>
    cases h with
    | auxApp hq ha => simp only [shift,shiftTerm _ q _ amount d hq hc,shiftTerm _ a _ amount d ha hc]
termination_by sizeOf q

theorem shiftBases (C : Spine.BoundContext) (As : NArgs) (types : List Ty) (amount d : Nat)
    (h : BaseTyped C As types) (hc : Below C d) : shiftArgs amount d As = As := by
  cases As with
  | nil => rfl
  | cons q qs =>
    cases h with
    | cons hq hs => simp only [shiftArgs,shiftTerm _ q _ amount d hq hc,shiftBases _ qs _ amount d hs hc]
termination_by sizeOf As

theorem shiftExtras (C : Spine.BoundContext) (As : NArgs) (amount d : Nat)
    (h : ExtrasTyped C As) (hc : Below C d) : shiftArgs amount d As = As := by
  cases As with
  | nil => rfl
  | cons q qs =>
    cases h with
    | cons hq hs => simp only [shiftArgs,shiftTerm _ q _ amount d hq hc,shiftExtras _ qs amount d hs hc]
termination_by sizeOf As
end

end LogicLineages.PersistentMarking.NumberedWindowClosingScopeProof
