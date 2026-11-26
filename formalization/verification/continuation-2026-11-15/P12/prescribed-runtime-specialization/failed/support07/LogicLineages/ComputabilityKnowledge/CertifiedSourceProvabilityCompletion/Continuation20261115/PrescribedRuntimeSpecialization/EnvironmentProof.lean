module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EnvironmentProof
open GorbowSyntax FixedFormulaSubstitution List.Vector
theorem liftRuntime (n : Nat) :
 liftEnvironment (runtimeEnvironment n) = headEnvironment n := by
 funext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => rfl
theorem specializeHead (n : Nat) :
 UniformRuntimeEnvironmentAgreement.specialize (headEnvironment n) = runtimeEnvironment (n+1) := by
 funext i
 cases i using Fin.cases with
 | zero => simp [UniformRuntimeEnvironmentAgreement.specialize,headEnvironment,runtimeEnvironment]
 | succ i => simp [UniformRuntimeEnvironmentAgreement.specialize,headEnvironment,runtimeEnvironment]
theorem allValue {n ctx : Nat} (ctag atag : Nat) (f : Formula (n+1))
 (raw : List.Vector (Term ctx) n) :
 value ctag atag (.all f) raw =
 unaryValue ctag 10 (formulaValue ctag atag raw f (headEnvironment n)) := by
 simp only [value,formulaValue,liftRuntime]
theorem stepValue {n ctx : Nat} (ctag atag : Nat) (f : Formula (n+1))
 (raw : List.Vector (Term ctx) (n+1)) :
 UniformRuntimeSpecializationStep.body ctag atag (headEnvironment n) f raw.tail raw.head =
 value ctag atag f raw := by
 rw [UniformRuntimeSpecializationStep.body,specializeHead]
 have hraw : raw.head ::ᵥ raw.tail = raw := List.Vector.cons_head_tail raw
 exact congrArg (fun v : List.Vector (Term ctx) (n+1) =>
  formulaValue ctag atag v f (runtimeEnvironment (n+1))) hraw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EnvironmentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EnvironmentProof
