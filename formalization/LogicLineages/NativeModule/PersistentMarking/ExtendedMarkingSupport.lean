module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedMarkingTargets
public import LogicLineages.NativeModule.PersistentMarking.ExtendedEndpointProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementMarkProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedMarkingSupport
open Spine NameBridge ElementarySupportProof

theorem annotation (q : Expr) : (headmark q).type = q.type := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | head f base => rfl
  | marked f τ base extras => rfl
  | lam σ q => simp only [headmark,Expr.type,annotation q]
termination_by sizeOf q

theorem names (n : Name) (q : Expr) : freeOccurs n (headmark q) = freeOccurs n q := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | head f base => simp [headmark,freeOccurs,freeOccursArgs]
  | marked f τ base extras => rfl
  | lam σ q => exact names n q
termination_by sizeOf q

theorem opening (σ : Ty) (x d : Nat) (q : Expr) :
    headmark (substitute (.cons (.free σ x) .nil) d q) =
      substitute (.cons (.free σ x) .nil) d (headmark q) := by
  cases q with
  | free δ y => rfl
  | bound δ i =>
    by_cases hi : i < d
    · simp [substitute,hi,headmark]
    · cases hn : i-d with
      | zero => simp [substitute,hi,hn,Args.get,shift,headmark]
      | succ n => simp [substitute,hi,hn,Args.get,headmark]
  | head f base => rfl
  | marked f τ base extras => rfl
  | lam δ q => simp only [substitute,headmark,opening σ x (d+1) q]
termination_by sizeOf q

theorem typedBack (Γ : BoundContext) (q : Expr) (σ : Ty)
    (h : Typed Γ (headmark q) σ) : Typed Γ q σ := by
  cases q with
  | free δ x => exact h
  | bound δ i => exact h
  | marked f τ base extras => exact h
  | head f base => cases h with | marked hb he => exact .head hb
  | lam δ q => cases h with | lam hb => exact .lam (typedBack _ q _ hb)
termination_by sizeOf q

theorem validForward (S : Signature) (q : Expr) (h : Valid S q) : Valid S (headmark q) := by
  cases q with
  | free δ x => exact h
  | bound δ i => exact h
  | marked f τ base extras => exact h
  | head f base => exact ⟨h.1,h.2,True.intro⟩
  | lam δ q => exact validForward S q h
termination_by sizeOf q

theorem validBack (S : Signature) (q : Expr) (h : Valid S (headmark q)) : Valid S q := by
  cases q with
  | free δ x => exact h
  | bound δ i => exact h
  | marked f τ base extras => exact h
  | head f base => exact ⟨h.1,h.2.1⟩
  | lam δ q => exact validBack S q h
termination_by sizeOf q

theorem paperForward (S : Signature) (q : Expr) (σ : Ty) (h : PaperTerm S q σ) : PaperTerm S (headmark q) σ :=
  ⟨SpineMarkingProof.headmarkTyped _ q σ h.1,validForward S q h.2⟩
theorem paperBack (S : Signature) (q : Expr) (σ : Ty) (h : PaperTerm S (headmark q) σ) : PaperTerm S q σ :=
  ⟨typedBack _ q σ h.1,validBack S q h.2⟩
end LogicLineages.PersistentMarking.ExtendedMarkingSupport
