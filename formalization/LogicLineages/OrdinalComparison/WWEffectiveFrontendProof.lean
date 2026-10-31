module
public import LogicLineages.OrdinalComparison.WWEffectiveFrontendTargets
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge

private theorem frontendPointComputable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (fun q xs => codedQueryAt (f q) xs) := by
  have heval : Computable₂ codedQueryAt := encodedQueryCodecCorrect.2.2
  apply (heval.comp (hf.comp Computable.fst) Computable.snd).of_eq
  intro p
  rfl

private noncomputable def frontendBad (f : Nat → Nat) : Nat → Nat → Bool :=
  SourceCounterBoundBox.radiusBad (fun q => queryArity (f q)) (fun q xs => codedQueryAt (f q) xs)

private theorem frontendBadComputable (f : Nat → Nat) (hf : Computable f) : Computable₂ (frontendBad f) :=
  SourceCounterBoundBox.radiusComputable _ _ (encodedQueryCodecCorrect.2.1.comp hf)
    (frontendPointComputable f hf)

private theorem frontendGood (f : Nat → Nat) (q : Nat) :
    SourceCounterBoundSearch.Good (frontendBad f) q ↔ CodedQueryGood (f q) :=
  SourceCounterBoundBox.exhaustive _ _ q

private theorem frontendGoodEq (f : Nat → Nat) :
    SourceCounterBoundSearch.Good (frontendBad f) = (fun q => CodedQueryGood (f q)) :=
  funext fun q => propext (frontendGood f q)

theorem effectiveFrontendCounterEnumerable : Targets.EffectiveFrontendCounterEnumerable := by
  intro f hf
  have h := SourceCounterBoundSearch.complementEnumerable (frontendBad f) (frontendBadComputable f hf)
  rwa [frontendGoodEq f] at h

private theorem frontendBound (f : Nat → Nat) :
    SourceCounterBoundSearch.HasComputableBound (frontendBad f) ↔ Targets.FrontendCoordinateBound f := by
  constructor
  · rintro ⟨b, hb, hbound⟩
    refine ⟨b, hb, ?_⟩
    intro q hq
    obtain ⟨r, hr, hbad⟩ := hbound q (fun h => hq ((frontendGood f q).mp h))
    obtain ⟨xs, hlen, hcoords, hp⟩ :=
      (SourceCounterBoundBox.radiusCorrect (fun q => queryArity (f q))
        (fun q xs => codedQueryAt (f q) xs) q r).mp hbad
    exact ⟨xs, hlen, fun x hx => (hcoords x hx).trans hr, hp⟩
  · rintro ⟨b, hb, hbound⟩
    refine ⟨b, hb, ?_⟩
    intro q hq
    obtain ⟨xs, hlen, hcoords, hp⟩ := hbound q (fun h => hq ((frontendGood f q).mpr h))
    exact ⟨b q, le_rfl,
      (SourceCounterBoundBox.radiusCorrect (fun q => queryArity (f q))
        (fun q xs => codedQueryAt (f q) xs) q (b q)).mpr ⟨xs, hlen, hcoords, hp⟩⟩

theorem effectiveFrontendDecisionIffCoordinateBound : Targets.EffectiveFrontendDecisionIffCoordinateBound := by
  intro f hf
  have h := SourceCounterBoundSearch.decisionIffBound (frontendBad f) (frontendBadComputable f hf)
  rw [frontendGoodEq f] at h
  exact h.trans (frontendBound f)
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
