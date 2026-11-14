module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel
open GorbowPRProgram
/-- The existing literal saturating wrapper applied to the unchanged reflexivity CORE checker. -/
abbrev checker (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (TwoSol20261113.ReflexivityCertificate.checker old arithmetic x)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel
