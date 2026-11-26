module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector

/-- Two genuine object-language existential witnesses; every source code is covered. -/
def pairSurjective {ctx : Nat} (tag : Nat) (code : Term ctx) : Formula ctx :=
  .ex (.ex (.equal (HistoryKernel.pairCall tag (.var 1) (.var 0))
    (SixSol20261112.Fuel.liftTerm (SixSol20261112.Fuel.liftTerm code))))

/-- Arbitrary runtime iteration count and arbitrary raw remaining-line code.
The sole logical premise is an actual successful old iteration. -/
def iteratorSuffix {ctx : Nat} (itag atag ptag : Nat)
    (count index fuel h tail lines out rest : Term ctx) : Formula ctx :=
  .imp
    (.equal (SixSol20261112.HistoryMachine.iterationCall itag count
      (HistoryKernel.pairCall ptag (.succ h) lines) index fuel)
      (HistoryKernel.pairCall ptag (.succ out) rest))
    (.equal (SixSol20261112.HistoryMachine.iterationCall itag count
      (HistoryKernel.pairCall ptag (.succ (HistoryKernel.pairCall atag h tail)) lines) index fuel)
      (HistoryKernel.pairCall ptag (.succ (HistoryKernel.pairCall atag out tail)) rest))

/-- Clause on precisely the existing literal-source witnesses and addresses. -/
def iteratorClause (pF : Program 1) (valid logical arithmetic : Program 1)
    (axiomProgram : Program 3) (bound initial : Program 1) (finalizer : Program 4)
    (appendOffset : Nat) : Sentence :=
  GorbowStandardInduction.universalClosure
    (iteratorSuffix
      (SixSol20261112.HistoryMachine.iteratorTag (GorbowNamedInternalProvability.checkerTag pF)
        (HistoryKernel.kernel valid logical arithmetic axiomProgram) bound initial finalizer)
      (LiteralKernelSource.appendTag pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset)
      (LiteralKernelSource.pairTag pF valid logical arithmetic axiomProgram bound initial finalizer)
      (.var (0 : Fin 8)) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix
