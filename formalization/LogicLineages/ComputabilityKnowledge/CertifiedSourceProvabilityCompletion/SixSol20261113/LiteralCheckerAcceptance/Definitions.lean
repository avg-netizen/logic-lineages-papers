module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance
open GorbowSyntax GorbowPRProgram GorbowPRChildTags GorbowPRDefiningEquations List.Vector
open LiteralCheckerAuxiliaries

/-- Original core input order is index, fuel, context, formula, certificate. -/
def coreCall {ctx : Nat} (tag : Nat) (index fuel context formula certificate : Term ctx) : Term ctx :=
  call tag (index ::ᵥ fuel ::ᵥ context ::ᵥ formula ::ᵥ certificate ::ᵥ nil)

def iteratorOffset (v l a : Program 1) (x : Program 3) : Nat :=
  argumentTag finalizer (SixSol20261112.HistoryMachine.checkerArguments
    (HistoryKernel.kernel v l a x) bound initial) 0 + 1

def runCall {ctx : Nat} (itag ptag : Nat) (index fuel certificate : Term ctx) : Term ctx :=
  SixSol20261112.HistoryMachine.iterationCall itag certificate
    (HistoryKernel.pairCall ptag (.succ .zero) certificate) index fuel

/-- The encoded certificate is the iteration bound, NOT its list length. -/
def normalization {ctx : Nat} (qtag itag ftag ptag : Nat)
    (index fuel context formula certificate : Term ctx) : Formula ctx :=
  .equal (coreCall qtag index fuel context formula certificate)
    (finalCall ftag (runCall itag ptag index fuel certificate) context formula certificate)

/-- Positive existential witnesses: outer raw code, inner history tail. The
sorted formula code equals raw+raw in this exact orientation. All remaining
lines are zero by internal drain, not a validity or native calibration premise. -/
def successfulWitness {ctx : Nat} (itag ptag ctag : Nat)
    (index fuel context formula certificate : Term ctx) : Formula ctx :=
  let lift2 : Term ctx → Term (ctx+1+1) := fun t =>
    SixSol20261112.Fuel.liftTerm (SixSol20261112.Fuel.liftTerm t)
  .ex (.ex (.conj
    (.equal (lift2 formula) (.add (.var (Fin.succ (0 : Fin (ctx+1)))) (.var (Fin.succ (0 : Fin (ctx+1))))))
    (.equal (runCall itag ptag (lift2 index) (lift2 fuel) (lift2 certificate))
      (successfulState ptag ctag (lift2 context) (.var (Fin.succ (0 : Fin (ctx+1)))) (.var 0) .zero))))

def acceptance {ctx : Nat} (qtag itag ptag ctag : Nat)
    (index fuel context formula certificate : Term ctx) : Formula ctx :=
  let accepted := Formula.equal (coreCall qtag index fuel context formula certificate) (.succ .zero)
  let witness := successfulWitness itag ptag ctag index fuel context formula certificate
  .conj (.imp accepted witness) (.imp witness accepted)

def acceptanceClause (pF : Program 1) (v l a : Program 1) (x : Program 3) : Sentence :=
  GorbowStandardInduction.universalClosure
    (acceptance (coreTag pF v l a x) (loopTag pF v l a x+1)
      (LiteralKernelSource.pairTag pF v l a x bound initial finalizer)
      (LiteralKernelSource.consTag pF v l a x bound initial finalizer)
      (.var (0 : Fin 5)) (.var 1) (.var 2) (.var 3) (.var 4))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance
