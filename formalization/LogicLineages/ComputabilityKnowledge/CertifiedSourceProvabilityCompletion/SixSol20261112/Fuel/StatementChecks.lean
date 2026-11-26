module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Proof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.StatementChecks

theorem nativeSaturation : Targets.NativeSaturation := NativeProof.nativeSaturation
theorem sameNumericChecker : Targets.SameNumericChecker := NativeProof.sameNumericChecker
theorem openStep : Targets.OpenStep := StepProof.openStep
theorem openIncrement : Targets.OpenIncrement := InductionProof.openIncrement
theorem openMonotonicity : Targets.OpenMonotonicity := InductionProof.openMonotonicity
theorem sameSourceFuelInvariant : Targets.SameSourceFuelInvariant := Proof.sameSourceFuelInvariant

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel
