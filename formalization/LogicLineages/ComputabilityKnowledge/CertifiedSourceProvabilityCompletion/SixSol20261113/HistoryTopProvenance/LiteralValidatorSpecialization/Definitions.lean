module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.BooleanProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.LineBindingProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization
open GorbowSyntax GorbowPRProgram
/-- Function child of the ACTUAL literal line-validator occurrence in the
iterator. This is not an independently calibrated old existential leaf. -/
def formulaTag (itag : Nat) (l a : Program 1) (x : Program 3) : Nat :=
 validityTag itag LiteralSyntaxValidator.lineValidator l a x + 1

def conclusion {ctx : Nat} (itag ptag ctag ftag : Nat)
 (count lines context raw tail remaining index fuel : Term ctx) : Formula ctx :=
 .imp (.equal (HistoryRunSplice.run itag ptag count (.succ .zero) lines index fuel)
   (HistoryRunSplice.state ptag
     (.succ (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail)) remaining))
   (.equal (LiteralSyntaxValidator.formulaCall ftag context raw) (.succ .zero))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization
