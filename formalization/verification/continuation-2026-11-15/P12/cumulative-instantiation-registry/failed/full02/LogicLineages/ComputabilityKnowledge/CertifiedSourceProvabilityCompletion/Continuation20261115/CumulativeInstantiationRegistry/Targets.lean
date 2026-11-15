module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Targets
open GorbowSyntax GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Unconditional joint installation in the explicit finite carrier. No registry
membership, source, runtime success or abstract Installation premise. -/
def FiniteInstallation : Prop := ∀ (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (x : Program 3),
 Nonempty (JointInstallation (carrier lhs rhs t old a x) lhs rhs t old a x)
/-- One concrete finite registry and its witnesses are fixed before all runtime
values/index/fuel and symbolic raw terms. Both old arithmetic compiler and new
fixed equality-instantiation certificates coexist at the same new actual CORE. -/
def OneRuntimePackage : Prop := ∀ (lhs rhs : Term 1) k (t : Term k),
 ArithmeticTemplateEvaluation.Arithmetic t →
 ∀ (old a : Program 1) (x : Program 3),
 ∃ I : JointInstallation (carrier lhs rhs t old a x) lhs rhs t old a x,
 CompilerCapability lhs rhs t old a x I ∧ InstantiationCapability lhs rhs t old a x I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Targets
