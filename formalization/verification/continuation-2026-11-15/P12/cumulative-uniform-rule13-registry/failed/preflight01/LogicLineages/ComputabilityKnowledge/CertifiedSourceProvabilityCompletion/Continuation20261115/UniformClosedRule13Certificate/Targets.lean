module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Certificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Certificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- One substantive joint certificate contract: actual singleton run, CORE and
Fuel at the same index/fuel/code. Count is the encoded certificate NUMBER, not
length1. Both runtime codes are arbitrary; only original guards are hypotheses.
C is the actual predecessor(case13[two arguments]), never a substituted image. -/
def InternalCertificate : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (formula replacement index fuel : Term ctx),
 let C := UniformClosedRule13.conclusionValue I.caseTag I.predTag I.ctag formula replacement
 let code := certificate I.ctag I.constructorTag formula replacement
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards I.fval I.vtag formula replacement)
   (.conj
    (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel code)
     (output I.ptag I.ctag I.caseTag I.predTag formula replacement))
    (.conj
     (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Certificate.Targets
