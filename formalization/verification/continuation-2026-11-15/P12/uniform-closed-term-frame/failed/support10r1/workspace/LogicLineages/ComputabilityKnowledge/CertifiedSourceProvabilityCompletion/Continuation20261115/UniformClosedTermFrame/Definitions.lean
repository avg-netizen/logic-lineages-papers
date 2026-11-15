module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame
open GorbowSyntax SixSol20261113
/-- Literal original term task, with arbitrary symbolic bound and untouched
runtime rest. Packed state uses the original Option successor and pair codec. -/
def initial {ctx : Nat} (ptag ctag : Nat) (bound rest out : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag
  (.succ (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 bound) rest)) out
/-- Joint successful residual task stack and exact appended raw output. -/
def final {ctx : Nat} (ptag atag : Nat) (rest out tokens : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (.succ rest) (HistoryAppend.appendCall atag out tokens)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame
