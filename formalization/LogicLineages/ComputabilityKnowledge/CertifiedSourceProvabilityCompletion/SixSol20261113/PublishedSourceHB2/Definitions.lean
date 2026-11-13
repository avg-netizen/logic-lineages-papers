module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB
/-- The original published HB2 sentence, retaining the literal conditional
provability Pr_D(sigma)=Pr_S(rho→sigma). Its Sentence arguments are external,
exactly as in SelectedCertifiedPresentation; this is not an internal universal
schema over arbitrary numeric syntax codes. -/
def hb2Clause (pF : Program 1) (c : Code) (sigma tau : Sentence) : Sentence :=
 GorbowPublishedLobReduction.hb2 pF c sigma tau
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2
