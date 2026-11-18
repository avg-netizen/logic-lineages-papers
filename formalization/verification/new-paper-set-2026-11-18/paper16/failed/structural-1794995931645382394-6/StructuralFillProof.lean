import LogicLineages.PersistentMarking.ClosingProof
namespace LogicLineages.PersistentMarking.StructuralFillProof
open Spine NameBridge StructuralContext

theorem typedAppend (Γ : BoundContext) (xs ys : Args) (as bs : List Ty)
    (hx : BaseTyped Γ xs as) (hy : BaseTyped Γ ys bs) :
    BaseTyped Γ (xs.append ys) (as ++ bs) := by
  cases hx with
  | nil => exact hy
  | cons hq hqs => exact .cons hq (typedAppend _ _ _ _ _ hqs hy)
termination_by sizeOf xs

theorem validAppend (S : Signature) (xs ys : Args) (hx : ValidArgs S xs) (hy : ValidArgs S ys) :
    ValidArgs S (xs.append ys) := by
  cases xs with
  | nil => exact hy
  | cons q qs => exact ⟨hx.1,validAppend S qs ys hx.2 hy⟩
termination_by sizeOf xs

theorem ordinaryAppend (xs ys : Args) (hx : OrdinaryArgs xs) (hy : OrdinaryArgs ys) :
    OrdinaryArgs (xs.append ys) := by
  cases xs with
  | nil => exact hy
  | cons q qs => exact ⟨hx.1,ordinaryAppend qs ys hx.2 hy⟩
termination_by sizeOf xs

theorem fillPaper : StructuralStabilityTargets.FillPaper := by
  intro S C σ τ q hc hq
  induction hc with
  | hole => exact hq
  | head hc ha hb hvb hob he hve hoe hargs ih =>
    constructor
    · apply Typed.head
      rw [hargs]
      exact typedAppend _ _ _ _ _ hb (.cons (ih hq).1 he)
    · exact ⟨ha,validAppend S _ _ hvb ⟨(ih hq).2,hve⟩⟩
  | bind hc ih =>
    exact ⟨.lam (ClosingProof.closeTyped _ _ _ (ih hq).1),ClosingProof.closeValidity _ _ _ (ih hq).2⟩

theorem fillOrdinary : StructuralStabilityTargets.FillOrdinary := by
  intro S C σ τ q hc hq
  induction hc with
  | hole => exact hq
  | head hc ha hb hvb hob he hve hoe hargs ih =>
    exact ordinaryAppend _ _ hob ⟨ih,hoe⟩
  | bind hc ih => exact ClosingProof.closeOrdinary _ _ ih
end LogicLineages.PersistentMarking.StructuralFillProof
