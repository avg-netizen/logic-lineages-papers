module

public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceSubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionSourceCallSupport
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof

theorem consumeSubtype (σ : Ty) (args : Args) (τ : Ty) (h : consumeTypes σ args = some τ) : τ ∈ subtypes σ := by
  cases args with
  | nil => simp only [consumeTypes,Option.some.injEq] at h; subst τ; exact subtypeSelf σ
  | cons a rest => cases σ with
    | ground => cases h
    | arrow α β =>
      by_cases he : a.type = α
      · simp only [consumeTypes,if_pos he] at h
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (consumeSubtype β rest τ h))
      · simp [consumeTypes,he] at h
termination_by sizeOf args

theorem appendUniverse (K V H Γ xs ys) (hx : ArgsUniverse K V H Γ xs) (hy : ArgsUniverse K V H Γ ys) :
    ArgsUniverse K V H Γ (xs.append ys) := by
  cases xs with
  | nil => exact hy
  | cons x xs => exact ⟨hx.1,appendUniverse K V H Γ xs ys hx.2 hy⟩
termination_by sizeOf xs

theorem callExtras (Γ : BoundContext) (σ : Ty) (args : Args) (τ : Ty) (h : CallTyped Γ σ args τ) : ExtrasTyped Γ args := by
  induction h with
  | nil => exact .nil
  | cons hq hqs ih => exact .cons hq ih
end LogicLineages.PersistentMarking.DecisionSourceCallSupport
