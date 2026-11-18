import LogicLineages.PersistentMarking.RefinementTransitivitySupport
namespace LogicLineages.PersistentMarking.RefinementTransitivityProof
open Spine NameBridge RefinementMeasure RefinementTransitivitySupport OpeningFoundationProof

theorem compose (S : Signature) (n : Nat) : ∀ q s (right : RefinementTree S q s),
    treeSize right = n → ∀ p, RefinementTree S p q → Refines S p s := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q s right hn p left
    have smaller : Smaller S n := by
      intro q s r hr p l
      exact ih (treeSize r) hr q s r rfl p l
    cases right with
    | var => cases left; exact ⟨.var⟩
    | @head f qs ss hp hs hb =>
      cases left with
      | head hl hm lb =>
        have hb' : basesSize hb < n := by change 1 + basesSize hb = n at hn; omega
        obtain ⟨out⟩ := composeBases S n smaller _ _ hb hb' _ lb
        exact ⟨.head hl hs out⟩
    | @marked f τ qb qe sb se hp hs hb he =>
      cases left with
      | marked hl hm lb le =>
        have hb' : basesSize hb < n := by change 1 + basesSize hb + extrasSize he = n at hn; omega
        have he' : extrasSize he < n := by change 1 + basesSize hb + extrasSize he = n at hn; omega
        obtain ⟨outb⟩ := composeBases S n smaller _ _ hb hb' _ lb
        obtain ⟨oute⟩ := composeExtras S n smaller f qb qe se he he' _ _ τ (.marked hl hm lb le)
        exact ⟨.marked hl hs outb oute⟩
    | @abs σ q τ s x hp hs hxq hxs hc =>
      cases left with
      | @abs _ p τl _ y hl hm hyp hyq lc =>
        have ht : Ty.arrow σ τl = Ty.arrow σ τ :=
          (SpineShiftProof.annotationExact _ _ _ hm.1).symm.trans (SpineShiftProof.annotationExact _ _ _ hp.1)
        have hτ : τl = τ := (Ty.arrow.inj ht).2
        have hl' : PaperTerm S (.lam σ p) (.arrow σ τ) := by simpa only [hτ] using hl
        let z := max (maxFreeName p) (max (maxFreeName q) (maxFreeName s)) + 1
        have hzp : freeOccurs (σ,z) p = false := aboveFresh σ z p (by dsimp [z]; omega)
        have hzq : freeOccurs (σ,z) q = false := aboveFresh σ z q (by dsimp [z]; omega)
        have hzs : freeOccurs (σ,z) s = false := aboveFresh σ z s (by dsimp [z]; omega)
        obtain ⟨lc',hle⟩ := RefinementOpeningProof.synchronize S σ y z p q hyp hyq hzp hzq lc
        obtain ⟨hc',hre⟩ := RefinementOpeningProof.synchronize S σ x z q s hxq hxs hzq hzs hc
        have hr : treeSize hc' < n := by
          change 1 + treeSize hc = n at hn
          omega
        obtain ⟨out⟩ := smaller hc' hr lc'
        exact ⟨.abs hl' hs hzp hzs out⟩

theorem transitive : RefinementSyntaxTargets.Transitive := by
  intro S q s t hqs hst
  obtain ⟨left⟩ := hqs
  obtain ⟨right⟩ := hst
  exact compose S (treeSize right) s t right rfl q left
end LogicLineages.PersistentMarking.RefinementTransitivityProof
