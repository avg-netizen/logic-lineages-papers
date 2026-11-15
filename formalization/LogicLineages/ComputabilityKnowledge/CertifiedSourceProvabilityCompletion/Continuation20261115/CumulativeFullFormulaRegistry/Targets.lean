module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.Targets
open GorbowSyntax GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
def FiniteInstallation : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (x : Program 3),
 Nonempty (JointInstallation (carrier f lhs rhs t old a x) f lhs rhs t old a x)
/-- Same chosen actual installation before all four runtime capabilities.
No cross-registry tag equality or Theory inclusion is a premise. -/
def OneRuntimePackage : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k),
 ArithmeticTemplateEvaluation.Arithmetic t → ∀ (old a : Program 1) (x : Program 3),
 ∃ I : JointInstallation (carrier f lhs rhs t old a x) f lhs rhs t old a x,
 CompilerCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I ∧
 EqualityCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I ∧
 FullFormulaCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I ∧
 RetentionCapability (carrier f lhs rhs t old a x) f lhs rhs t old a x I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.Targets
