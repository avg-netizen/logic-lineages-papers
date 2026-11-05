module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10AdapterSemanticProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10AdapterProgramsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Proof
open LogicLineages.ComputabilityKnowledge
open CircuitLinear

private theorem input_after_parse (e : Nat) (xs : List Nat) (p : PolynomialCircuit.Code)
    (he : Encodable.decode e=some xs) (hp : PolynomialCircuit.decode xs=some p)
    (hw : p.WellFormed) :
    DiophantineCompletion.encodedPolynomialSolvable e ↔ PolynomialDomainShift.HasNonnegativeRoot p := by
  constructor
  · rintro ⟨ys,q,hy,hq,hqw,hroot⟩
    have hys : ys=xs := Option.some.inj (hy.symm.trans he)
    subst ys
    have hqp : q=p := Option.some.inj (hq.symm.trans hp)
    subst q
    exact hroot
  · intro hroot
    exact ⟨xs,p,he,hp,hw,hroot⟩

private theorem output_after_encode (c : SystemCode) (hw : WellFormedCode c) :
    encodedPolynomialSolvable (Encodable.encode c) ↔ PolynomialSatisfiable (systemOfCode c) := by
  constructor
  · rintro ⟨d,hd,hdw,hs⟩
    have he : c=d := Option.some.inj ((Encodable.encodek c).symm.trans hd)
    subst d
    exact hs
  · intro hs
    exact ⟨c,Encodable.encodek c,hw,hs⟩

/-- The actual total map, with all parse failures and invalid original indices
sent to the proved impossible system. No undecidability premise is assumed. -/
theorem codedH10ToLinearSystems : H10ReductionTargets.CodedH10ToLinearSystems := by
  refine ⟨reduce,reductionPrimitive.to_comp,?_⟩
  intro e
  cases he : (Encodable.decode e : Option (List Nat)) with
  | none =>
    have hleft : ¬ DiophantineCompletion.encodedPolynomialSolvable e := by
      rintro ⟨xs,p,hx,_⟩
      rw [he] at hx
      cases hx
    have hr : reduce e=impossibleCode := by
      simp only [reduce,he,Option.map_none,Option.getD_none]
    rw [hr]
    exact iff_of_false hleft impossibleSystemCorrect.2
  | some xs =>
    by_cases hv : H10Validity.validInput xs=true
    · obtain ⟨p,hp,hw⟩ := (H10Validity.Proof.inputValidity xs).mp hv
      have hcw := (PolynomialCircuitProof.compiledWellFormed
        (PolynomialDomainShift.shift p) (PolynomialDomainShiftProof.wellFormedPreserved p hw)).2
      have hfull := CircuitFull.Proof.full_circuit_encoding
        (PolynomialCircuit.compile (PolynomialDomainShift.shift p)) hcw
      have hr : reduce e=Encodable.encode
          (encodeCircuitSystem (PolynomialCircuit.compile (PolynomialDomainShift.shift p))) := by
        simp only [reduce,he,Option.map_some,Option.getD_some]
        exact parsedCalibration xs p hp hw
      rw [hr]
      exact (input_after_parse e xs p he hp hw).trans
        ((polynomialCircuitRoot p hw).trans (hfull.2.trans (output_after_encode _ hfull.1).symm))
    · have hleft : ¬ DiophantineCompletion.encodedPolynomialSolvable e := by
        rintro ⟨ys,p,hy,hp,hw,hroot⟩
        have hys : ys=xs := Option.some.inj (hy.symm.trans he)
        subst ys
        exact hv ((H10Validity.Proof.inputValidity xs).mpr ⟨p,hp,hw⟩)
      have hf : H10Validity.validInput xs=false := Bool.eq_false_iff.mpr hv
      have hr : reduce e=impossibleCode := by
        simp only [reduce,he,Option.map_some,Option.getD_some]
        exact originalSafety xs hf
      rw [hr]
      exact iff_of_false hleft impossibleSystemCorrect.2

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Proof
