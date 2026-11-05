module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10AdapterTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityProgramsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericProgramsProof
public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftEffectivityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Proof
open LogicLineages.ComputabilityKnowledge

/-- Every stage is a concrete primitive-recursive finite-code operation;
representation existence is not used as an algorithm. -/
theorem reductionPrimitive : Targets.ReductionPrimitive := by
  have hstage : Primrec (fun xs : List Nat =>
      (PolynomialCircuit.compileCode xs).bind CircuitNumeric.encode) :=
    Primrec.option_bind PolynomialCircuitEffectivityProof.compilerPrimrec
      (CircuitNumeric.Proof.encoderPrimitive.comp Primrec.snd).to₂
  have hshift : Primrec (fun xs : List Nat =>
      (PolynomialDomainShift.encodedShift xs).bind fun shifted =>
        (PolynomialCircuit.compileCode shifted).bind CircuitNumeric.encode) :=
    Primrec.option_bind PolynomialDomainShiftEffectivityProof.shiftPrimrec
      (hstage.comp Primrec.snd).to₂
  have ht : Primrec translate :=
    Primrec.ite (Primrec.eq.comp H10Validity.Proof.validityPrimitive (Primrec.const true))
      (Primrec.option_getD.comp hshift (Primrec.const impossibleCode))
      (Primrec.const impossibleCode)
  exact Primrec.option_getD.comp
    (Primrec.option_map (Primrec.decode (α := List Nat)) (ht.comp Primrec.snd).to₂)
    (Primrec.const impossibleCode)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Proof
