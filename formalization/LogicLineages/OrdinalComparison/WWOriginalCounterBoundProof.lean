module
public import LogicLineages.OrdinalComparison.WWOriginalCounterBoundTargets
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendProof
public import LogicLineages.OrdinalComparison.WWEffectiveFrontendProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalInput
open ForwardTranslation

theorem originalFrontendBoundEquivalence : Targets.OriginalFrontendBoundEquivalence := by
  constructor
  · rintro ⟨b,hb,h⟩
    refine ⟨b,hb,?_⟩
    intro n hn
    obtain ⟨xs,hlen,hcoords,hbad⟩ := h n (fun hg => hn ((originalInputFrontendGoodCorrect n).mp hg))
    refine ⟨xs,hlen.trans (originalInputFrontendArity n),hcoords,?_⟩
    intro hp
    have ht := (originalInputFrontendPointCorrect n xs).mpr hp
    rw [hbad] at ht
    exact Bool.false_ne_true ht
  · rintro ⟨b,hb,h⟩
    refine ⟨b,hb,?_⟩
    intro n hn
    obtain ⟨xs,hlen,hcoords,hbad⟩ := h n (fun hg => hn ((originalInputFrontendGoodCorrect n).mpr hg))
    refine ⟨xs,hlen.trans (originalInputFrontendArity n).symm,hcoords,?_⟩
    apply Bool.eq_false_iff.mpr
    intro ht
    exact hbad ((originalInputFrontendPointCorrect n xs).mp ht)

theorem originalSourceCounterEnumerable : Targets.OriginalSourceCounterEnumerable := by
  have h := effectiveFrontendCounterEnumerable frontend originalInputFrontendPrimitiveRecursive.to_comp
  exact h.of_eq (fun n => not_congr (originalInputFrontendGoodCorrect n))

theorem originalSourceDecisionIffBound : Targets.OriginalSourceDecisionIffBound := by
  have h := effectiveFrontendDecisionIffCoordinateBound frontend originalInputFrontendPrimitiveRecursive.to_comp
  constructor
  · intro hd
    have hc : ComputablePred (fun n => CodedQueryGood (frontend n)) :=
      hd.of_eq (fun n => (originalInputFrontendGoodCorrect n).symm)
    exact originalFrontendBoundEquivalence.mp (h.mp hc)
  · intro hb
    have hc := h.mpr (originalFrontendBoundEquivalence.mpr hb)
    exact hc.of_eq (fun n => originalInputFrontendGoodCorrect n)

theorem actualOriginalCounterBound : Targets.ActualOriginalCounterBound :=
  ⟨originalSourceCounterEnumerable, originalSourceDecisionIffBound⟩
end LogicLineages.OrdinalComparison.Source.OriginalInput
