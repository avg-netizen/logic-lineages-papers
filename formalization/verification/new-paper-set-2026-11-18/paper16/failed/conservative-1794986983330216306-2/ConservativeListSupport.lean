import LogicLineages.PersistentMarking.ConservativeTargets
import LogicLineages.PersistentMarking.OwnerRefinementProof
import LogicLineages.PersistentMarking.ComparisonOrdinaryProof
namespace LogicLineages.PersistentMarking.ConservativeListSupport
open Spine

theorem refiningPaper {S : Signature} {q s : Expr} {σ : Ty}
    (h : RefinementTree S q s) (hs : PaperTerm S s σ) : PaperTerm S q σ := by
  have hq := (RefinementSubstitutionSupport.endpoints h).1
  have he := (RefinementTransitivitySupport.annotation h).trans (SpineShiftProof.annotationExact _ _ _ hs.1)
  exact he ▸ hq

theorem baseAt {S : Signature} {qs ss : Args} (h : RefinementBasesTree S qs ss) {i s} (ha : At ss i s) :
    ∃ q, At qs i q ∧ Refines S q s := by
  cases ss with
  | nil => cases ha
  | cons s ss =>
    cases h with
    | cons h hs =>
      cases ha with
      | here => exact ⟨_,.here,⟨h⟩⟩
      | there ha =>
        obtain ⟨q,hq,hr⟩ := baseAt hs ha
        exact ⟨q,.there hq,hr⟩
termination_by sizeOf ss

theorem transportRemove {S : Signature} {qs ss rest : Args} {s : Expr}
    (h : RefinementBasesTree S qs ss) (hr : Remove ss s rest) :
    ∃ q qrest, Remove qs q qrest ∧ Refines S q s ∧ _root_.Nonempty (RefinementBasesTree S qrest rest) := by
  cases hr with
  | here =>
    cases h with
    | cons h hs => exact ⟨_,_,.here,⟨h⟩,⟨hs⟩⟩
  | there hr =>
    cases h with
    | cons h hs =>
      obtain ⟨q,qr,hrem,href,htail⟩ := transportRemove hs hr
      obtain ⟨ht⟩ := htail
      exact ⟨q,_,.there hrem,href,⟨.cons h ht⟩⟩
termination_by sizeOf ss

theorem transportSplit {S : Signature} {qs ss kept removed : Args}
    (h : RefinementBasesTree S qs ss) (hs : Split ss kept removed) :
    ∃ qk qr, Split qs qk qr ∧ _root_.Nonempty (RefinementBasesTree S qk kept) ∧ _root_.Nonempty (RefinementBasesTree S qr removed) := by
  cases hs with
  | nil => cases h; exact ⟨.nil,.nil,.nil,⟨.nil⟩,⟨.nil⟩⟩
  | left hs =>
    cases h with
    | cons h ht =>
      obtain ⟨qk,qr,hsp,hk,hr⟩ := transportSplit ht hs
      obtain ⟨hk⟩ := hk
      exact ⟨_,qr,.left hsp,⟨.cons h hk⟩,hr⟩
  | right hs =>
    cases h with
    | cons h ht =>
      obtain ⟨qk,qr,hsp,hk,hr⟩ := transportSplit ht hs
      obtain ⟨hr⟩ := hr
      exact ⟨qk,_,.right hsp,hk,⟨.cons h hr⟩⟩
termination_by sizeOf ss

theorem baseNonempty {S : Signature} {qs ss : Args} (h : RefinementBasesTree S qs ss) (hn : Spine.Nonempty ss) : Spine.Nonempty qs := by
  cases h with
  | nil => exact hn
  | cons _ _ => trivial

theorem splitOrdinary {xs ys zs : Args} (h : Split xs ys zs) (ho : OrdinaryArgs xs) : OrdinaryArgs ys ∧ OrdinaryArgs zs := by
  induction h with
  | nil => exact ⟨True.intro,True.intro⟩
  | left h ih =>
    have hh := ih ho.2
    exact ⟨⟨ho.1,hh.1⟩,hh.2⟩
  | right h ih =>
    have hh := ih ho.2
    exact ⟨hh.1,⟨ho.1,hh.2⟩⟩
theorem removeOrdinaryParts {xs rest : Args} {x : Expr} (h : Remove xs x rest) (ho : OrdinaryArgs xs) : Ordinary x ∧ OrdinaryArgs rest := by
  induction h with
  | here => exact ho
  | there h ih =>
    have hh := ih ho.2
    exact ⟨hh.1,⟨ho.1,hh.2⟩⟩

end LogicLineages.PersistentMarking.ConservativeListSupport
