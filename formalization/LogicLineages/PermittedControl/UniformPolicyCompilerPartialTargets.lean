module
public import LogicLineages.PermittedControl.PolicySuppliedCodeMacroInterpreterTargets
public import LogicLineages.StandardControlCurrent.PolicyPartialDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.UniformPolicyCompiler
open OrdinalComparison Source Source.AdmissibleSum
open PolicySuppliedCodeMacro (RealizesPolicy)

/-- Layer 1 of the uniform compiler: the policy partial recursion with the
policy program as a runtime input, calibrated on realizing programs. -/
def ExactUniformPartial : Prop :=
  ∃ runPart : Nat.Partrec.Code × Nat × Nat × Nat →. Option (List Nat), Partrec runPart ∧
    ∀ (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
      ∀ level i n : Nat, runPart (e,level,i,n) = Part.some (StandardControlCurrent.PolicyPartial.run p level i n)

end LogicLineages.PermittedControl.UniformPolicyCompiler
