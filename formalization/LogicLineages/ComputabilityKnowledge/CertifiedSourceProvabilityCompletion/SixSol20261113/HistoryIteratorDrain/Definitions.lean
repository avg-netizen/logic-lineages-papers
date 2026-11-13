module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain
open GorbowSyntax GorbowPRProgram GorbowPRChildTags GorbowPRDefiningEquations List.Vector

def dropCall {ctx : Nat} (tag : Nat) (count lines : Term ctx) : Term ctx :=
  call tag (count ::ᵥ lines ::ᵥ nil)
def remainingCall {ctx : Nat} (dtag itag ptag : Nat)
    (count option lines index fuel : Term ctx) : Term ctx :=
  call dtag (SixSol20261112.HistoryMachine.iterationCall itag count
    (HistoryKernel.pairCall ptag option lines) index fuel ::ᵥ nil)

/-- Actual right decoder in the installed kernel's stateLines test. -/
def rightTag (pF : Program 1) (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) : Nat :=
  LiteralKernelSource.kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer +
    argumentTag HistoryCodec.select (HistoryKernel.TransitionEquationsProof.kernelArguments valid logical arithmetic axiomProgram) 0 + 1

/-- The count is the raw encoded remaining-line code, exactly the external
boundFunction's value. This does not identify the opaque bound AST internally. -/
def drainClause (pF : Program 1) (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) : Sentence :=
  GorbowStandardInduction.universalClosure
    (.equal (remainingCall
      (rightTag pF valid logical arithmetic axiomProgram bound initial finalizer)
      (SixSol20261112.HistoryMachine.iteratorTag (GorbowNamedInternalProvability.checkerTag pF)
        (HistoryKernel.kernel valid logical arithmetic axiomProgram) bound initial finalizer)
      (LiteralKernelSource.pairTag pF valid logical arithmetic axiomProgram bound initial finalizer)
      (.var (1 : Fin 4)) (.var 0) (.var 1) (.var 2) (.var 3)) .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain
