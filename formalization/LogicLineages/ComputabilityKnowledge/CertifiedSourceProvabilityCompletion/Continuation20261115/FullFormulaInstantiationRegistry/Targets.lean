module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry.Targets
open GorbowSyntax GorbowPRProgram
/-- All twelve concrete AST memberships are witnessed, not supplied. -/
def FiniteInstallation : Prop := ∀ (f : Formula 1) (old arithmetic : Program 1) (x : Program 3),
 Nonempty (FullFormulaInstantiationCertificate.Installation (carrier f old arithmetic x) f old arithmetic x)
/-- One concrete carrier and installation chosen before every runtime input.
Actual singleton run, CORE and Fuel are supplied jointly by internal derivation. -/
def OneRuntimePackage : Prop := ∀ (f : Formula 1) (old arithmetic : Program 1) (x : Program 3),
 ∃ I : FullFormulaInstantiationCertificate.Installation (carrier f old arithmetic x) f old arithmetic x,
 RuntimeCapability f old arithmetic x I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry.Targets
