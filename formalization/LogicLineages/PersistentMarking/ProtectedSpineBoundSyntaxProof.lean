import LogicLineages.PersistentMarking.ProtectedSpineBoundTargets
import LogicLineages.PersistentMarking.SpineSubstitutionProof

namespace LogicLineages.PersistentMarking.ProtectedSpineBoundSyntaxProof
open Spine

theorem prefixAt (types : List Ty) (C : BoundContext) (i : Nat) :
    BoundContext.prefix types C i = if i < types.length then types[i]? else C (i-types.length) := by
  induction types generalizing i with
  | nil => simp [BoundContext.prefix]
  | cons σ types ih =>
    cases i with
    | zero => simp [BoundContext.prefix,BoundContext.push]
    | succ i =>
      simpa [BoundContext.prefix,BoundContext.push,Nat.succ_lt_succ_iff,Nat.succ_sub_succ_eq_sub] using ih i

theorem emptyPrefix (types : List Ty) (i : Nat) : BoundContext.prefix types EmptyContext i = types[i]? := by
  rw [prefixAt]
  by_cases h : i < types.length
  · simp [h]
  · simp [h,EmptyContext,List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem getTyped (vs : Args) (types : List Ty) (h : BaseTyped EmptyContext vs types)
    (i : Nat) (σ : Ty) (hi : types[i]? = some σ) :
    ∃ v, vs.get i = some v ∧ Typed EmptyContext v σ := by
  cases vs with
  | nil => cases h; simp at hi
  | cons v vs =>
    cases h with
    | cons hv hvs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
        exact ⟨v,rfl,hi ▸ hv⟩
      | succ i =>
        obtain ⟨w,hw,ht⟩ := getTyped vs _ hvs i σ hi
        exact ⟨w,hw,ht⟩
termination_by sizeOf vs

theorem compatible (vs : Args) (removed kept : List Ty) (h : BaseTyped EmptyContext vs removed) :
    SubCompatible vs kept.length (BoundContext.prefix kept (BoundContext.prefix removed EmptyContext))
      (BoundContext.prefix kept EmptyContext) := by
  induction kept with
  | nil => exact SpineSubstitutionProof.finiteCompatible _ _ _ h
  | cons σ kept ih =>
    exact SpineSubstitutionProof.compatiblePush _ _ _ _ ih σ

end LogicLineages.PersistentMarking.ProtectedSpineBoundSyntaxProof
