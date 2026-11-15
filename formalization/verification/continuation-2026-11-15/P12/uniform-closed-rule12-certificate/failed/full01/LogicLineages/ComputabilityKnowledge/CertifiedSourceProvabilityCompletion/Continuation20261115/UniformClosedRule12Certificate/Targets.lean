module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- One substantive joint certificate contract: actual singleton run, CORE and
Fuel at the same index/fuel/code. Count is the encoded certificate NUMBER, not
length1. All three runtime codes are arbitrary; only original guards are hypotheses.
C is the actual predecessor(case12[three arguments]), never a substituted image. -/
def InternalCertificate : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (formula leftTerm rightTerm index fuel : Term ctx),
 let C := UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm
 let code := certificate I.ctag I.constructorTag formula leftTerm rightTerm
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm)
   (.conj
    (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel code)
     (output I.ptag I.ctag I.caseTag I.predTag formula leftTerm rightTerm))
    (.conj
     (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.Targets
