module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.Targets
open GorbowSyntax GorbowPRProgram
/-- One concrete cumulative installation selected before all runtime inputs:
original compiler/quotation, equality/fixedformula certificates and arbitrary
old CORE success are retained, alongside the new uniform joint certificate. -/
def OneRuntimePackage : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k),
 Continuation20261114.ArithmeticTemplateEvaluation.Arithmetic t → ∀ (old a : Program 1) (x : Program 3),
 ∃ I : JointInstallation (carrier f lhs rhs t old a x) f lhs rhs t old a x,
 CompilerCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I ∧
 EqualityCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I ∧
 FullFormulaCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I ∧
 RetentionCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I ∧
 UniformCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.Targets
