import LogicLineages.PersistentMarking.StructuralHeadSupport
namespace LogicLineages.PersistentMarking.StructuralHeadProof
open Spine StructuralHeadSupport StructuralFillProof

theorem paper (S : Signature) (f : Head) (before after : Args) (bt at : List Ty) (q : Expr) (τ : Ty)
    (hf : Admitted S f) (hb : BaseTyped EmptyContext before bt) (hvb : ValidArgs S before)
    (ha : BaseTyped EmptyContext after at) (hva : ValidArgs S after)
    (hargs : f.arguments = bt ++ τ :: at) (hq : PaperTerm S q τ) :
    PaperTerm S (.head f (before.append (.cons q after))) f.result := by
  constructor
  · apply Typed.head
    rw [hargs]
    exact typedAppend _ _ _ _ _ hb (.cons hq.1 ha)
  · exact ⟨hf,validAppend S _ _ hvb ⟨hq.2,hva⟩⟩

theorem weak (S : Signature) (f : Head) (before after : Args) (bt at : List Ty) (s t : Expr) (τ : Ty)
    (hf : Admitted S f) (hb : BaseTyped EmptyContext before bt) (hvb : ValidArgs S before) (hob : OrdinaryArgs before)
    (ha : BaseTyped EmptyContext after at) (hva : ValidArgs S after) (hoa : OrdinaryArgs after)
    (hargs : f.arguments = bt ++ τ :: at) (hs : PaperTerm S s τ) (ht : PaperTerm S t τ)
    (hw : Weak S s t) :
    Weak S (.head f (before.append (.cons s after))) (.head f (before.append (.cons t after))) := by
  obtain ⟨rank,hr⟩ := hf
  exact .funHead (paper S f before after bt at s τ ⟨rank,hr⟩ hb hvb ha hva hargs hs)
    (paper S f before after bt at t τ ⟨rank,hr⟩ hb hvb ha hva hargs ht) ⟨rank,hr,hr⟩ rfl
    (matchingSlot S before after bt at s t hb hvb hob ha hva hoa hw)

theorem strict (S : Signature) (f : Head) (before after : Args) (bt at : List Ty) (s t : Expr) (τ : Ty)
    (hf : Admitted S f) (hb : BaseTyped EmptyContext before bt) (hvb : ValidArgs S before) (hob : OrdinaryArgs before)
    (ha : BaseTyped EmptyContext after at) (hva : ValidArgs S after) (hoa : OrdinaryArgs after)
    (hargs : f.arguments = bt ++ τ :: at) (hs : PaperTerm S s τ) (ht : PaperTerm S t τ)
    (hw : Strict S s t) :
    Strict S (.head f (before.append (.cons s after))) (.head f (before.append (.cons t after))) := by
  have hsource := paper S f before after bt at s τ hf hb hvb ha hva hargs hs
  have htarget := paper S f before after bt at t τ hf hb hvb ha hva hargs ht
  have hbsource : BaseTyped EmptyContext (before.append (.cons s after)) f.arguments := by
    rw [hargs]
    exact typedAppend _ _ _ _ _ hb (.cons hs.1 ha)
  have hvsource := validAppend S before (.cons s after) hvb ⟨hs.2,hva⟩
  have hmarked : PaperTerm S (.marked f f.result (before.append (.cons s after)) .nil) f.result :=
    ⟨.marked hbsource .nil,hf,hvsource,True.intro⟩
  obtain ⟨rank,hr⟩ := hf
  apply Strict.intro hsource htarget rfl
  apply Weak.stat hmarked htarget ⟨rank,hr,hr⟩
  · exact .replace (splitSlot before after s) (splitSlot before after t) True.intro
      (ElementaryProof.matchingRefl S (before.append after) (bt++at)
        (typedAppend _ _ _ _ _ hb ha) (validAppend S _ _ hvb hva) (ordinaryAppend _ _ hob hoa))
      (.cons .here hw .nil)
  · exact wholeSuppliers S f _ _ ⟨rank,hr⟩ hbsource hvsource
      (slotSuppliers S before after bt at s t hb hvb hob ha hva hoa (ElementaryProof.strictIncluded S s t hw))
end LogicLineages.PersistentMarking.StructuralHeadProof
