module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder
open GorbowPRProgram GorbowPRChildTags

/-- Literal ternary zero/positive branch, not an opaque PR witness. -/
def choose {n : Nat} (test yes no : Program n) : Program n :=
  .composition HistoryCodec.select (Fin.cases test (Fin.cases yes (Fin.cases no Fin.elim0)))

def candidateArguments : Fin 2 → Program 5 :=
  Fin.cases (.projection 2) (Fin.cases (.projection 0) Fin.elim0)
def candidate : Program 5 := .composition HistoryCodec.pair candidateArguments

def forwardArguments : Fin 2 → Program 5 :=
  Fin.cases candidate (Fin.cases (.projection 3) Fin.elim0)
def backwardArguments : Fin 2 → Program 5 :=
  Fin.cases (.projection 3) (Fin.cases candidate Fin.elim0)
def forward : Program 5 := .composition HistoryCodec.difference forwardArguments
def backward : Program 5 := .composition HistoryCodec.difference backwardArguments

/-- false selects first coordinate, true selects second coordinate.
Step inputs [b,previous,a,code,seed]; both truncated differences must vanish. -/
def stepArguments (right : Bool) : Fin 3 → Program 5 :=
  Fin.cases forward (Fin.cases
    (choose backward (.projection (if right then 0 else 2)) (.projection 1))
    (Fin.cases (.projection 1) Fin.elim0))
def innerStep (right : Bool) : Program 5 := .composition HistoryCodec.select (stepArguments right)
/-- [countB,a,code,seed], enumerate b=0,...,countB-1. -/
def inner (right : Bool) : Program 4 := .recursion (.projection 2) (innerStep right)

def outerArguments : Fin 4 → Program 3 :=
  Fin.cases (.composition .succ (fun _ => .projection 2))
    (Fin.cases (.projection 0) (Fin.cases (.projection 2) (Fin.cases (.projection 1) Fin.elim0)))
def outerStep (right : Bool) : Program 3 := .composition (inner right) outerArguments
/-- [countA,code], enumerate a=0,...,countA-1, scanning every b≤code. -/
def outer (right : Bool) : Program 2 := .recursion (SixSol20261112.Fuel.zeroProgram 1) (outerStep right)
def decoderArguments : Fin 2 → Program 1 :=
  Fin.cases (.composition .succ (fun _ => .projection 0)) (Fin.cases (.projection 0) Fin.elim0)
/-- Bounded exhaustive search of the actual square-shell codec, inclusive on
both coordinates. Existing pair bounds ensure coverage of every preimage. -/
def decoder (right : Bool) : Program 1 := .composition (outer right) decoderArguments

/-- Address of the first literal pair child, tracked through all actual AST nodes. -/
def pairTag (right : Bool) (tag : Nat) : Nat :=
  tag + 1 + stepTag (SixSol20261112.Fuel.zeroProgram 1) + 1 +
    stepTag (.projection (2 : Fin 3)) + argumentTag HistoryCodec.select (stepArguments right) 0 +
    argumentTag HistoryCodec.difference forwardArguments 0 + 1

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder
