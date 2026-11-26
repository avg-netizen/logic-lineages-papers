module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Actual original Some/default projection, never supplied successful output. -/
def instanceValue {n ctx : Nat} {p : Program n} (I : UniformClosedRule13Validity.Installation p)
 (matrix witness : Term ctx) : Term ctx :=
 call I.predTag (UniformClosedInstanceRecognizer.instanceCall I.itag matrix witness ::ᵥ nil)
def negValue {ctx : Nat} (ctag : Nat) (a : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.unaryValue ctag 6 a
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge
