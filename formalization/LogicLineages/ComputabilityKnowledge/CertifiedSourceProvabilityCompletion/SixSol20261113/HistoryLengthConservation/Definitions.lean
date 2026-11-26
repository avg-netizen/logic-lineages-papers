module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation
open GorbowSyntax
open HistoryRunSplice HistoryLengthOffset

/-- Successful actual full run at the original numeric certificate bound.
No relation between certificate code and true length is a premise. -/
def conservation {ctx : Nat} (itag ltag ptag : Nat) (lines history out index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (run itag ptag lines (.succ history) lines index fuel) (state ptag (.succ out) .zero))
    (.equal (lengthCall ltag out) (.add (lengthCall ltag history) (lengthCall ltag lines)))

/-- This is the exact equality needed to replace the original MP reference
antecedent-certificate length by antecedent-output-history length. -/
def emptyConservation {ctx : Nat} (itag ltag ptag : Nat) (lines out index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (run itag ptag lines (.succ .zero) lines index fuel) (state ptag (.succ out) .zero))
    (.equal (lengthCall ltag out) (lengthCall ltag lines))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation
