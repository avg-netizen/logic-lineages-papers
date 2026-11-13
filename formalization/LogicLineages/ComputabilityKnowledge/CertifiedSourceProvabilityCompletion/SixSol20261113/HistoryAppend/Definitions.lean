module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend
open GorbowPRProgram GorbowSyntax GorbowPRDefiningEquations List.Vector

/-- Table base stores append(0,right)=right as its only entry. -/
def tableBaseArguments : Fin 2 → Program 1 :=
  Fin.cases (.projection 0) (Fin.cases (SixSol20261112.Fuel.zeroProgram 1) Fin.elim0)
def tableBase : Program 1 := .composition HistoryCodec.cons tableBaseArguments

/-- Step inputs [n,previousTable,right]; compute append(succ n,right). -/
def inputCode : Program 3 := .composition .succ (fun _ => .projection 0)
def inputHead : Program 3 := .composition HistoryLookup.head (fun _ => inputCode)
def inputTail : Program 3 := .composition HistoryLookup.tail (fun _ => inputCode)
/-- Previous table lists results at codes n,n-1,...,0. -/
def referenceIndexArguments : Fin 2 → Program 3 :=
  Fin.cases inputTail (Fin.cases (.projection 0) Fin.elim0)
def referenceIndex : Program 3 := .composition HistoryCodec.difference referenceIndexArguments

def referenceArguments : Fin 2 → Program 3 :=
  Fin.cases referenceIndex (Fin.cases (.projection 1) Fin.elim0)
def reference : Program 3 := .composition HistoryLookup.lookup referenceArguments
/-- The referenced Option payload is extracted only where the internal table
coverage proof supplies SOME; no failure is reinterpreted as a valid reference. -/
def recursiveResult : Program 3 := .composition HistoryCodec.predecessor (fun _ => reference)
def valueArguments : Fin 2 → Program 3 :=
  Fin.cases inputHead (Fin.cases recursiveResult Fin.elim0)
def value : Program 3 := .composition HistoryCodec.cons valueArguments

def tableStepArguments : Fin 2 → Program 3 :=
  Fin.cases value (Fin.cases (.projection 1) Fin.elim0)
def tableStep : Program 3 := .composition HistoryCodec.cons tableStepArguments
/-- Inputs [leftCode,rightCode]. Finite course-of-values table, newest first. -/
def table : Program 2 := .recursion tableBase tableStep
/-- Actual runtime append, not a numeral-only syntactic prefix operation. -/
def append : Program 2 := .composition HistoryLookup.head (fun _ => table)

def appendCall {ctx : Nat} (tag : Nat) (left right : Term ctx) : Term ctx := call tag (left ::ᵥ right ::ᵥ nil)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend
