module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource
open GorbowSyntax GorbowPRProgram GorbowPRChildTags GorbowPublishedDCB
open SixSol20261112

/-- This is a NEW literal-kernel checker, selected before the source tuple.
No equality with the earlier opaque kernel AST is asserted. -/
def coreChecker (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) : Program 5 :=
  SixSol20261112.HistoryMachine.checker (HistoryKernel.kernel valid logical arithmetic axiomProgram) bound initial finalizer

def verifier (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) : Program 5 :=
  Fuel.verifier (coreChecker valid logical arithmetic axiomProgram bound initial finalizer)

/-- Actual iterator recursion step then its composition-function child. -/
def kernelTag (pF : Program 1) (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) : Nat :=
  SixSol20261112.HistoryMachine.iteratorTag (GorbowNamedInternalProvability.checkerTag pF)
    (HistoryKernel.kernel valid logical arithmetic axiomProgram) bound initial finalizer +
      stepTag SixSol20261112.HistoryMachine.iterationBase + 1

def appendTag (pF : Program 1) (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) (appendOffset : Nat) : Nat :=
  kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer+appendOffset

def pairTag (pF : Program 1) (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) : Nat :=
  HistoryKernel.TransitionEquationsProof.outputPairTag
    (kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer) valid logical arithmetic axiomProgram

def consTag (pF : Program 1) (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) : Nat :=
  HistoryKernel.EntryProof.outputConsTag (HistoryKernel.TransitionEquationsProof.someTag
    (kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer) valid logical arithmetic axiomProgram)

/-- Exact successful-step suffix law, universally closed over all seven runtime
terms. The append address is a witnessed subtree of THIS literal kernel. -/
def stepClause (pF : Program 1) (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) (appendOffset : Nat) : Sentence :=
  GorbowStandardInduction.universalClosure
    (HistoryKernel.stepSuffix
      (kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer)
      (appendTag pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset)
      (pairTag pF valid logical arithmetic axiomProgram bound initial finalizer)
      (consTag pF valid logical arithmetic axiomProgram bound initial finalizer)
      (.var (0 : Fin 7)) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource
