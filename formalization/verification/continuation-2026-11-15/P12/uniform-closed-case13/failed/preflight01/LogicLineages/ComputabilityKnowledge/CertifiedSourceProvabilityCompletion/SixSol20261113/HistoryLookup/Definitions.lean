module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup
open GorbowPRProgram GorbowSyntax GorbowPRDefiningEquations List.Vector

/-- Both destructors use literal predecessor then the checked literal decoder. -/
def head : Program 1 := .composition (HistoryDecoder.decoder false) (fun _ => HistoryCodec.predecessor)
def tail : Program 1 := .composition (HistoryDecoder.decoder true) (fun _ => HistoryCodec.predecessor)
def dropStep : Program 3 := .composition tail (fun _ => .projection 1)
/-- Inputs [index,encodedHistory]; literal repeated tail. -/
def drop : Program 2 := .recursion (.projection 0) dropStep
/-- Encode Option Entry: empty suffix is NONE=0, nonempty suffix is
SOME head=succ(headCode). Thus entry code zero remains distinguishable from failure. -/
def referenceArguments : Fin 3 → Program 1 :=
  Fin.cases (.projection 0) (Fin.cases (SixSol20261112.Fuel.zeroProgram 1)
    (Fin.cases (.composition .succ (fun _ => head)) Fin.elim0))
def reference : Program 1 := .composition HistoryCodec.select referenceArguments
/-- Actual getElem? reference operation, with Option-encoded output. -/
def lookup : Program 2 := .composition reference (fun _ => drop)

def consCall {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx := call tag (a ::ᵥ b ::ᵥ nil)
def lookupCall {ctx : Nat} (tag : Nat) (index code : Term ctx) : Term ctx := call tag (index ::ᵥ code ::ᵥ nil)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup
