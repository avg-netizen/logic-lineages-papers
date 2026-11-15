module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB
abbrev verifier (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 UniformClosedRule13Certificate.verifier old arithmetic (SixSol20261113.SaturatedAxiomLeaf.saturated x)
abbrev root (pF pR old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 FiniteRuleFourCertificate.root pF pR (UniformClosedRule13.logicalLeaf old) arithmetic x
/-- Original rule4 singleton, with its original List Line numeric codec. -/
def seed {n : Nat} (f : Formula n) : Nat :=
 FiniteRuleFourCertificate.certificateCode (GorbowStandardInduction.universalClosure f)
def certificate {n ctx : Nat} (mtag ctag atag constructorTag : Nat) (f : Formula n)
 (raw : List.Vector (Term ctx) n) : Term ctx :=
 PrescribedRuntimeSpecialization.certificate mtag ctag atag constructorTag f raw (Term.numeral (seed f))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization
