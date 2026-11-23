module

public import LogicLineages.NativeModule.PersistentMarking.PrefixEscapeSupportTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ClosedSyntaxProof
open Spine

def Bounded (Γ : BoundContext) (d : Nat) : Prop := ∀ i σ, Γ i = some σ → i < d

theorem pushBound {Γ : BoundContext} {d : Nat} (h : Bounded Γ d) (σ : Ty) : Bounded (Γ.push σ) (d+1) := by
  intro i τ hi
  cases i with
  | zero => omega
  | succ i =>
    have hh : Γ i = some τ := hi
    have hl := h i τ hh
    omega

mutual
 theorem term (Γ : BoundContext) (d : Nat) (hb : Bounded Γ d) (q : Expr) (σ : Ty)
    (ht : Typed Γ q σ) (k : Nat) (vs : Args) : shift k d q = q ∧ substitute vs d q = q := by
  cases q with
  | free τ x => exact ⟨rfl,rfl⟩
  | bound τ i =>
    cases ht with
    | bound hi =>
      have hlt := hb i _ hi
      constructor <;> simp only [shift,substitute,hlt,if_true]
  | lam τ q =>
    cases ht with
    | lam ht =>
      have hh := term (Γ.push τ) (d+1) (pushBound hb τ) q _ ht k vs
      exact ⟨congrArg (Expr.lam τ) hh.1,congrArg (Expr.lam τ) hh.2⟩
  | head f qs =>
    cases ht with
    | head ht =>
      have hh := bases Γ d hb qs _ ht k vs
      exact ⟨congrArg (Expr.head f) hh.1,congrArg (Expr.head f) hh.2⟩
  | marked f τ qs es =>
    cases ht with
    | marked ht he =>
      have hh := bases Γ d hb qs _ ht k vs
      have hx := extras Γ d hb es he k vs
      constructor <;> simp only [shift,substitute,hh.1,hh.2,hx.1,hx.2]
 termination_by sizeOf q
 theorem bases (Γ : BoundContext) (d : Nat) (hb : Bounded Γ d) (qs : Args) (types : List Ty)
    (ht : BaseTyped Γ qs types) (k : Nat) (vs : Args) : shiftArgs k d qs = qs ∧ substituteArgs vs d qs = qs := by
  cases qs with
  | nil => exact ⟨rfl,rfl⟩
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      have hh := term Γ d hb q _ hq k vs
      have hs := bases Γ d hb qs _ hqs k vs
      constructor <;> simp only [shiftArgs,substituteArgs,hh.1,hh.2,hs.1,hs.2]
 termination_by sizeOf qs
 theorem extras (Γ : BoundContext) (d : Nat) (hb : Bounded Γ d) (qs : Args)
    (ht : ExtrasTyped Γ qs) (k : Nat) (vs : Args) : shiftArgs k d qs = qs ∧ substituteArgs vs d qs = qs := by
  cases qs with
  | nil => exact ⟨rfl,rfl⟩
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      have hh := term Γ d hb q _ hq k vs
      have hs := extras Γ d hb qs hqs k vs
      constructor <;> simp only [shiftArgs,substituteArgs,hh.1,hh.2,hs.1,hs.2]
 termination_by sizeOf qs
end

theorem emptyBound : Bounded EmptyContext 0 := by intro i σ hi; simp [EmptyContext] at hi

theorem closedShift : PrefixEscapeSupportTargets.ClosedShift := by
  intro q σ ht k
  exact (term EmptyContext 0 emptyBound q σ ht k .nil).1
theorem closedSubstitute : PrefixEscapeSupportTargets.ClosedSubstitute := by
  intro q σ ht vs
  exact (term EmptyContext 0 emptyBound q σ ht 0 vs).2
end LogicLineages.PersistentMarking.ClosedSyntaxProof
