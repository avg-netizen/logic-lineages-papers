module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeOwnerSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.SharpSelectionProof
open Spine ConservativeListSupport ConservativeOwnerSupport

theorem selectCase (S : Signature) (f : Head) (τ : Ty) (sb se qb qe : Args) (t q r : Expr) (domains : List Ty) (args : Args)
    (hs : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S t τ)
    (href : RefinementTree S (.marked f τ qb qe) (.marked f τ sb se))
    (ha : At sb i q ∨ At se i q) (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (hargs : PrefixTuple f sb se domains args) (hcall : apply q args = some r)
    (cont : ∀ p, Refines S p r → ExtendedWeak S p t) : ExtendedWeak S (.marked f τ qb qe) t := by
  have hp := refiningPaper href hs
  have hcopies := OwnerRefinementProof.refinedCopies S f τ qb qe sb se domains args ⟨href⟩ hargs
  have hta := tupleTyped S f τ qb qe hp (wholeTuple f qb qe domains) τ
  have htb := tupleTyped S f τ sb se hs hargs τ
  have hqt := SpineShiftProof.annotationExact _ _ _ hq
  have supply : (∃ a j, (At qb j a ∨ At qe j a) ∧ Refines S a q) ∨
      Refines S (.marked f q.type qb qe) q := by
    cases href with
    | marked _ _ hb he =>
      rcases ha with hab | hae
      · obtain ⟨a,hat,har⟩ := baseAt hb hab
        exact Or.inl ⟨a,i,Or.inl hat,har⟩
      · obtain ⟨h⟩ := RefinementTransitivitySupport.pickExtra he hae
        cases h with
        | existing hat har => exact Or.inl ⟨_,_,Or.inr hat,⟨har⟩⟩
        | owner har => exact Or.inr ⟨har⟩
  rcases supply with ⟨a,j,hat,har⟩ | har
  · obtain ⟨harTree⟩ := har
    have hap : PaperTerm S a (ArrowPrefix domains τ) := by
      have ha' := (RefinementSubstitutionSupport.endpoints harTree).1
      have he := (RefinementTransitivitySupport.annotation harTree).trans hqt
      exact he ▸ ha'
    have hatype := SpineShiftProof.annotationExact _ _ _ hap.1
    obtain ⟨p,hpCall,hpr⟩ := RefinementFullCallProof.fullApplication S a q (ownerCopies f qb qe domains) args τ r ⟨harTree⟩ hcopies
      (by rw [hatype]; exact hta) (by rw [hqt]; exact htb) hcall
    obtain ⟨hc⟩ := cont p hpr
    exact ⟨.select hp ht hat hap.1 hpCall hc⟩
  · rw [hqt] at har
    obtain ⟨p,hpCall,hpr⟩ := RefinementFullCallProof.fullApplication S (.marked f (ArrowPrefix domains τ) qb qe) q (ownerCopies f qb qe domains) args τ r har hcopies
      hta (by rw [hqt]; exact htb) hcall
    have hpExact := ownerApplication S f τ qb qe hp domains
    have heq : p = .marked f τ qb (qe.append (ownerCopies f qb qe domains)) := Option.some.inj (hpCall.symm.trans hpExact)
    subst p
    exact cont _ (RefinementTransitivityProof.transitive S _ _ _ (ownerExpansion S f τ qb qe hp domains) hpr)
end LogicLineages.PersistentMarking.SharpSelectionProof
