module
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundTargets
public import LogicLineages.OrdinalComparison.WWEncodedComparisonProof
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearchProof
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundBoxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge

private theorem decode_primitive : Primrec decodeArityQuery :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, false, (0, []), (0, [])))

theorem encodedQueryCodecCorrect : Targets.EncodedQueryCodecCorrect := by
  refine ⟨?_, (Primrec.fst.comp decode_primitive).to_comp, ?_⟩
  · intro q
    simp [decodeArityQuery]
  · have heval : Computable (fun p : EncodedQuery × List Nat => encodedQueryAt p.1 p.2) := encodedQueryAtComputable
    have hq : Computable (fun p : Nat × List Nat => (decodeArityQuery p.1).2) :=
      ((Primrec.snd.comp decode_primitive).to_comp.comp Computable.fst)
    apply (heval.comp (hq.pair Computable.snd)).of_eq
    intro p
    rfl

private noncomputable def bad : Nat → Nat → Bool :=
  SourceCounterBoundBox.radiusBad queryArity codedQueryAt

private theorem bad_computable : Computable₂ bad :=
  SourceCounterBoundBox.radiusComputable queryArity codedQueryAt
    encodedQueryCodecCorrect.2.1 encodedQueryCodecCorrect.2.2

private theorem good_equiv (q : Nat) : SourceCounterBoundSearch.Good bad q ↔ CodedQueryGood q :=
  SourceCounterBoundBox.exhaustive queryArity codedQueryAt q

private theorem good_eq : SourceCounterBoundSearch.Good bad = CodedQueryGood :=
  funext fun q => propext (good_equiv q)

theorem encodedQueryCounterEnumerable : Targets.EncodedQueryCounterEnumerable := by
  have h := SourceCounterBoundSearch.complementEnumerable bad bad_computable
  rwa [good_eq] at h

private theorem bound_equiv : SourceCounterBoundSearch.HasComputableBound bad ↔ CodedCoordinateBound := by
  constructor
  · rintro ⟨b, hb, hbound⟩
    refine ⟨b, hb, ?_⟩
    intro q hq
    obtain ⟨r, hr, hbad⟩ := hbound q (fun h => hq ((good_equiv q).mp h))
    obtain ⟨xs, hlen, hcoords, hp⟩ :=
      (SourceCounterBoundBox.radiusCorrect queryArity codedQueryAt q r).mp hbad
    exact ⟨xs, hlen, fun x hx => (hcoords x hx).trans hr, hp⟩
  · rintro ⟨b, hb, hbound⟩
    refine ⟨b, hb, ?_⟩
    intro q hq
    obtain ⟨xs, hlen, hcoords, hp⟩ := hbound q (fun h => hq ((good_equiv q).mpr h))
    exact ⟨b q, le_rfl,
      (SourceCounterBoundBox.radiusCorrect queryArity codedQueryAt q (b q)).mpr
        ⟨xs, hlen, hcoords, hp⟩⟩

theorem encodedQueryDecisionIffCoordinateBound : Targets.EncodedQueryDecisionIffCoordinateBound := by
  have h := SourceCounterBoundSearch.decisionIffBound bad bad_computable
  rw [good_eq] at h
  exact h.trans bound_equiv
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
