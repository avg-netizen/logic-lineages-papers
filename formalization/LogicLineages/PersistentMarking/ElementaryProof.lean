import LogicLineages.PersistentMarking.ElementarySupportProof
namespace LogicLineages.PersistentMarking.ElementaryProof
open Spine NameBridge ElementarySupportProof

theorem liftMark (S : Signature) (q r t : Expr) (σ : Ty)
    (hq : PaperTerm S q σ) (ht : PaperTerm S t σ)
    (hm : mark q = some r) (hw : Weak S r t) : Weak S q t := by
  cases q with
  | free δ x => simp [mark] at hm
  | bound δ i => simp [mark] at hm
  | head f base =>
    simp only [mark,Option.some.injEq] at hm
    subst r
    obtain ⟨hqt,hqv⟩ := hq
    cases hqt with
    | head hb => exact .put ⟨.head hb,hqv⟩ ht hw
  | marked f τ base extras =>
    simp only [mark,Option.some.injEq] at hm
    subst r
    exact hw
  | lam δ body =>
    cases hbmark : mark body with
    | none => simp [mark,hbmark] at hm
    | some b =>
      simp only [mark,hbmark,Option.map_some,Option.some.injEq] at hm
      subst r
      cases hw with
      | @abs δ b τ targetBody x hmarked htarget hfb hft hbody =>
        have htype : σ = .arrow δ τ :=
          (SpineShiftProof.annotationExact _ _ _ ht.1).symm.trans
            (SpineShiftProof.annotationExact _ _ _ htarget.1)
        subst σ
        have hf : freeOccurs (δ,x) body = false := (markNames (δ,x) body b hbmark).trans hfb
        have hopened := markSubstitution (.cons (.free δ x) .nil) 0 body b hbmark
        have hdepth := markedSpineDepth (.cons (.free δ x) .nil) 0 body b hbmark
        exact .abs hq htarget hf hft
          (liftMark S (openBody δ x body) (openBody δ x b) (openBody δ x targetBody) τ
            (openingPaper S δ τ x body hq) (openingPaper S δ τ x targetBody htarget) hopened hbody)
termination_by spineDepth q
decreasing_by all_goals simp_all [openBody,spineDepth] <;> omega

theorem strictIncluded : ComparisonTargets.StrictIncluded := by
  intro S q t h
  cases h with
  | intro hq ht hm hw => exact liftMark S q _ t _ hq ht hm hw

mutual
 theorem weakRefl (S : Signature) (q : Expr) (σ : Ty)
    (hp : PaperTerm S q σ) (ho : Ordinary q) : Weak S q q := by
  cases q with
  | free δ x => exact .var
  | bound δ i =>
    cases hp.1 with
    | bound hi => simp [EmptyContext] at hi
  | lam δ body =>
    cases hp.1 with
    | lam hb =>
      obtain ⟨x,hf,_⟩ := OpeningFoundationProof.freshOpeningExists δ body body
      exact .abs hp hp hf hf
        (weakRefl S (openBody δ x body) _ (openingPaper S δ _ x body hp) (openOrdinary δ x 0 body ho))
  | head f base =>
    cases hp.1 with
    | head hb =>
      obtain ⟨rank,hr⟩ := hp.2.1
      exact .funHead hp hp ⟨rank,hr,hr⟩ rfl (matchingRefl S base _ hb hp.2.2 ho)
  | marked f τ base extras => exact False.elim ho
 termination_by nodes q
 decreasing_by all_goals simp_all [nodes,argsNodes,openBody,openNodes] <;> omega
 theorem matchingRefl (S : Signature) (qs : Args) (types : List Ty)
    (ht : BaseTyped EmptyContext qs types) (hv : ValidArgs S qs) (ho : OrdinaryArgs qs) : Matching S qs qs := by
  cases qs with
  | nil => exact .nil
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      exact .cons .here (weakRefl S q _ ⟨hq,hv.1⟩ ho.1)
        (matchingRefl S qs _ hqs hv.2 ho.2)
 termination_by argsNodes qs
 decreasing_by all_goals simp_all [nodes,argsNodes] <;> omega
end

theorem ordinaryReflexive : ComparisonTargets.OrdinaryReflexive := weakRefl
end LogicLineages.PersistentMarking.ElementaryProof
