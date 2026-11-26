module
public import LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundEffectiveProof
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundBoxProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCounterBound

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent LogicLineages.ComputabilityKnowledge
open OriginalInput (Query decode)

def arity (n : Nat) : Nat := (decode n).1

noncomputable def codedTest (p : AdmissibleSum.Policy) (f : Nat → Nat) (n : Nat) (xs : List Nat) : Bool :=
  test p f (decode n) xs

noncomputable def bad (p : AdmissibleSum.Policy) (f : Nat → Nat) : Nat → Nat → Bool :=
  SourceCounterBoundBox.radiusBad arity (codedTest p f)

theorem bad_computable (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p)
    (f : Nat → Nat) (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable₂ (bad p f) := by
  have hd : Primrec decode := OriginalInput.originalInputCodecCorrect.2
  have ha : Primrec arity := Primrec.fst.comp hd
  have ht : Computable (fun x : Nat × List Nat => codedTest p f x.1 x.2) := by
    have hi : Computable (fun x : Nat × List Nat => (decode x.1, x.2)) :=
      (hd.to_comp.comp Computable.fst).pair Computable.snd
    have he : Computable (fun x : Query × List Nat => test p f x.1 x.2) := effective p hp f hc hf
    apply (he.comp hi).of_eq
    intro x
    rfl
  exact SourceCounterBoundBox.radiusComputable arity (codedTest p f) ha.to_comp ht

private theorem good_iff (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hf : FullAddition.Targets.SourceGrowth f) (q : Nat) :
    SourceCounterBoundSearch.Good (bad p f) q ↔ codedGood p f q := by
  change (∀ r : Nat, SourceCounterBoundBox.radiusBad arity (codedTest p f) q r = false) ↔
    Good p f (decode q)
  rw [SourceCounterBoundBox.exhaustive arity (codedTest p f) q, all_tuples]
  exact ⟨fun h xs hs => (pointCalibration p f hf _ xs hs).mp (h xs hs),
    fun h xs hs => (pointCalibration p f hf _ xs hs).mpr (h xs hs)⟩

private theorem bound_iff (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hf : FullAddition.Targets.SourceGrowth f) :
    SourceCounterBoundSearch.HasComputableBound (bad p f) ↔ CoordinateBound p f := by
  constructor
  · rintro ⟨b, hb, hbound⟩
    refine ⟨b, hb, fun q hq => ?_⟩
    obtain ⟨r, hr, hbad⟩ := hbound q (fun h => hq ((good_iff p f hf q).mp h))
    obtain ⟨xs, hlen, hs, ht⟩ := (SourceCounterBoundBox.radiusCorrect arity (codedTest p f) q r).mp hbad
    exact ⟨xs, hlen, fun x hx => (hs x hx).trans hr,
      fun hv => Bool.noConfusion (ht.symm.trans ((pointCalibration p f hf _ xs hlen).mpr hv))⟩
  · rintro ⟨b, hb, hbound⟩
    refine ⟨b, hb, fun q hq => ?_⟩
    obtain ⟨xs, hlen, hs, ht⟩ := hbound q (fun h => hq ((good_iff p f hf q).mpr h))
    refine ⟨b q, le_rfl, (SourceCounterBoundBox.radiusCorrect arity (codedTest p f) q (b q)).mpr
      ⟨xs, hlen, hs, ?_⟩⟩
    have hnot : codedTest p f q xs ≠ true := fun hv =>
      ht ((pointCalibration p f hf _ xs hlen).mp hv)
    exact Bool.eq_false_iff.mpr hnot

theorem full : CurrentCounterBoundTargets.Full := by
  intro p hp f hc hf
  have hbad := bad_computable p hp f hc hf
  have he : SourceCounterBoundSearch.Good (bad p f) = codedGood p f :=
    funext (fun q => propext (good_iff p f hf q))
  constructor
  · have h := SourceCounterBoundSearch.complementEnumerable (bad p f) hbad
    rwa [he] at h
  · have h := SourceCounterBoundSearch.decisionIffBound (bad p f) hbad
    rw [he] at h
    exact h.trans (bound_iff p f hf)

end LogicLineages.ControlSensitivityCurrent.CurrentCounterBound
