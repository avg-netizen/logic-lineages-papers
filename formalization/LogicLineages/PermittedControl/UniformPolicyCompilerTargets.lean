module
public import LogicLineages.PermittedControl.PolicySuppliedCodeMacroInterpreterTargets
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.UniformPolicyCompiler
open OrdinalComparison Source Source.AdmissibleSum Source.ForwardTranslation
open PolicySuppliedCodeMacro (RealizesPolicy)

/-- Calibration of one partial function on supplied policy programs: on every
program realizing a policy it halts on every raw context length and term code
and returns exactly the existing source compiler's output, including its
rejection `none`. Nothing is asked on programs realizing no policy. -/
def Calibrated (compilePolicy : Nat.Partrec.Code × Nat × Nat →. Option EncodedVector) : Prop :=
  ∀ (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
    ∀ d c : Nat, compilePolicy (e,d,c) = Part.some (StandardControlCurrent.PolicySourceInterface.compile p d c)

/-- The uniform source compiler: ONE partial recursive function taking the
policy program as a runtime input, calibrated to the existing compiler. The
existential is outside every quantifier over policies and programs. -/
def ExactUniformCompiler : Prop :=
  ∃ compilePolicy : Nat.Partrec.Code × Nat × Nat →. Option EncodedVector,
    Partrec compilePolicy ∧ Calibrated compilePolicy

end LogicLineages.PermittedControl.UniformPolicyCompiler
