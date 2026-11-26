import LogicLineages.PersistentMarking.ClosingProof
namespace LogicLineages.PersistentMarking.StructuralFillProof
open Spine NameBridge StructuralContext

theorem typedAppend (Γ : BoundContext) (xs ys : Args) (as bs : List Ty)
    (hx : BaseTyped Γ xs as) (hy : BaseTyped Γ ys bs) :
    BaseTyped Γ (xs.append ys) (as ++ bs) := by
  induction hx with
  | nil => exact hy
  | cons hq hqs ih => exact .cons hq ih

theorem validAppend (S : Signature) (xs ys : Args) (hx : ValidArgs S xs) (hy : ValidArgs S ys) :
    ValidArgs S (xs.append ys) := by
  induction xs with
  | nil => exact hy
  | cons q qs ih => exact ⟨hx.1,ih hx.2⟩

theorem ordinaryAppend (xs ys : Args) (hx : OrdinaryArgs xs) (hy : OrdinaryArgs ys) :
    OrdinaryArgs (xs.append ys) := by
  induction xs with
  | nil => exact hy
  | cons q qs ih => exact ⟨hx.1,ih hx.2⟩

theorem fillPaper : StructuralStabilityTargets.FillPaper := by
  intro S C σ τ q hc hq
  induction hc with
  | hole => exact hq
  | head hc ha hb hvb hob he hve hoe hargs ih =>
    constructor
    · apply Typed.head
      rw [hargs]
      exact typedAppend _ _ _ _ _ hb (.cons ih.1 he)
    · exact ⟨ha,validAppend S _ _ hvb ⟨ih.2,hve⟩⟩
  | bind hc ih =>
    exact ⟨.lam (ClosingProof.closeTyped _ _ _ ih.1),ClosingProof.closeValidity _ _ _ ih.2⟩

theorem fillOrdinary : StructuralStabilityTargets.FillOrdinary := by
  intro S C σ τ q hc hq
  induction hc with
  | hole => exact hq
  | head hc ha hb hvb hob he hve hoe hargs ih =>
    exact ordinaryAppend _ _ hob ⟨ih,hoe⟩
  | bind hc ih => exact ClosingProof.closeOrdinary _ _ ih
end LogicLineages.PersistentMarking.StructuralFillProof
