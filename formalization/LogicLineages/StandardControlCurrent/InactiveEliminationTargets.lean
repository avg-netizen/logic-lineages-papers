module
public import LogicLineages.StandardControlCurrent.InactiveEliminationDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveEliminationTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm InactiveElimination

def Cleaning : Prop :=
  (∀ (p : Formula) ν, (clean p).eval ν ↔ p.eval ν) ∧
  (∀ (p : Formula) j, j ∈ (clean p).variables → j ∈ p.variables) ∧
  (∀ (xs : List Nat) (p : Formula) i, i ∈ OrderedOccurrence.inactive xs p →
    LinearRows.isLinear i (clean p) = true)

def ActualNormalization : Prop := ∀ (xs : List Nat) (p : Formula) i,
  i ∈ OrderedOccurrence.inactive xs p → ∀ ν,
  (∃ n : Nat, p.eval (Function.update ν i n)) ↔
    ∃ n : Nat, LinearRows.unitEval (LinearRows.normalize i (clean p)) ν (n : Int)

/-- Complete finite candidate theorem, including arbitrary Boolean negations,
all signed residual rows, no lower-bound atom, and modulus one. -/
def CandidateCompleteness : Prop := ∀ (u : LinearRows.UnitFormula) (ν : Nat → Nat),
  0 < LinearRows.period u ∧
  ((∃ n : Nat, LinearRows.unitEval u ν (n : Int)) ↔
    ∃ b ∈ candidates u, (LinearRows.instantiate (LinearRows.guarded u) b).eval ν)

def Elimination : Prop := ∀ (xs : List Nat) (p : Formula) i,
  i ∈ OrderedOccurrence.inactive xs p → ∀ ν,
  (eliminate i p).eval ν ↔ ∃ n : Nat, p.eval (Function.update ν i n)

def Support : Prop := ∀ (p : Formula) i j,
  j ∈ (eliminate i p).variables → j ≠ i ∧ j ∈ p.variables

def BlockProgress : Prop := ∀ (xs : List Nat) (p : Formula) i,
  xs.Nodup → i ∈ OrderedOccurrence.inactive xs p →
  (xs.erase i).Nodup ∧ (xs.erase i).length+1=xs.length ∧
  (∀ ν, HyperCloseBlock.existsNames xs p.compile ν ↔
    HyperCloseBlock.existsNames (xs.erase i) (eliminate i p).compile ν) ∧
  (∀ j, j ∈ (eliminate i p).variables → j ∉ xs.erase i → j ∈ p.variables ∧ j ∉ xs)

/-- No global meaningfulness is inserted: the actual guarded atom stays under
any original Boolean negation before this transformation. -/
def GuardedAtom : Prop := ∀ (xs : List Nat) (a : Atom) i,
  i ∈ OrderedOccurrence.inactive xs (guardedAtom a) → ∀ ν,
  (eliminate i (guardedAtom a)).eval ν ↔
    ∃ n : Nat, rowMeaningful a.row (Function.update ν i n) ∧ a.eval (Function.update ν i n)

def Programs : Prop := Primrec Code.clean ∧ Primrec₂ Code.eliminate ∧
  (∀ p : Formula, Code.clean p.encode=(clean p).encode) ∧
  (∀ (i : Nat) (p : Formula), Code.eliminate i p.encode=(eliminate i p).encode)

def Full : Prop := Cleaning ∧ ActualNormalization ∧ CandidateCompleteness ∧ Elimination ∧
  Support ∧ BlockProgress ∧ GuardedAtom ∧ Programs
end LogicLineages.StandardControlCurrent.InactiveEliminationTargets
