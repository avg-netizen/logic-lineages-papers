module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector
open SixSol20261112.HistoryMachine

def state {ctx : Nat} (ptag : Nat) (option lines : Term ctx) : Term ctx := HistoryKernel.pairCall ptag option lines
/-- SAME index and fuel for every run in each splice law. -/
def run {ctx : Nat} (itag ptag : Nat) (count option lines index fuel : Term ctx) : Term ctx :=
  iterationCall itag count (state ptag option lines) index fuel

/-- Successful original encoded-bound prefix run, followed at true prefix length
in the concatenated input, leaving the right suffix untouched. -/
def prefixSplice {ctx : Nat} (itag ltag atag ptag : Nat)
    (left right history out index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (run itag ptag left (.succ history) left index fuel) (state ptag (.succ out) .zero))
    (.equal (run itag ptag (HistoryLengthOffset.lengthCall ltag left) (.succ history)
      (HistoryAppend.appendCall atag left right) index fuel) (state ptag (.succ out) right))

/-- Original encoded-code bounds on all THREE runs. Newest-first output order:
right output before left. No size/length arithmetic is assumed. -/
def appendRuns {ctx : Nat} (itag atag ptag : Nat)
    (left right outLeft outRight index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (run itag ptag left (.succ .zero) left index fuel) (state ptag (.succ outLeft) .zero))
    (.imp (.equal (run itag ptag right (.succ .zero) right index fuel) (state ptag (.succ outRight) .zero))
      (.equal (run itag ptag (HistoryAppend.appendCall atag left right) (.succ .zero)
          (HistoryAppend.appendCall atag left right) index fuel)
        (state ptag (.succ (HistoryAppend.appendCall atag outRight outLeft)) .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice
