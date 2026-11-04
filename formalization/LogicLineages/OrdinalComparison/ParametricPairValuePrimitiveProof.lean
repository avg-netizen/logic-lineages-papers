module
public import LogicLineages.OrdinalComparison.ParametricPairValuePrimitiveProgramsProof
public import LogicLineages.OrdinalComparison.ParametricFiniteCoefficientProof
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneProof
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive.Proof

theorem exactCalibration : Targets.ExactCalibration := by
  intro H hm hi p
  exact ParametricFiniteCoefficient.Proof.exactFiniteCoefficient
    (fun n => H (p.1,n)) (hm p.1) (hi p.1) p.2.1 p.2.2

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := by
  constructor
  · exact iterate_primitive
  · intro H hH hm hi
    exact (iterate_primitive H hH).of_eq (fun p => (exactCalibration H hm hi p).symm)

theorem fixedGammaPrimitive : Targets.FixedGammaPrimitive := by
  intro b
  let H : Nat × Nat → Nat := fun p => SourceMachineControlNonperiodicity.gamma b p.2
  have hH : Primrec H := (SourceMachineControlNonperiodicity.Proof.exactControlParity b).1.comp Primrec.snd
  obtain ⟨hm,hi,hrest⟩ := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  have h := uniformPrimitiveRecursive.2 H hH (fun _ => hm) (fun _ => hi)
  exact h.comp ((Primrec.const 0).pair Primrec.id)
end LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive.Proof
