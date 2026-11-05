module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsDefinitions
public import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsTargets
open NormalForm MaximalPlainRows

def ExactActiveGuard : Prop := ∀ (i : Nat) (r : Row) (ν : Nat → Nat),
  (activeGuard i r).eval ν ↔ PlainPhiDominance.active i r ν = true

def ActualSignedRowResidue : Prop := ∀ (i m : Nat), 0 < m →
  ∀ (r : Row) (ν : Nat → Nat), PlainPhiDominance.shiftMass r + m ≤ ν i →
    Int.ModEq (m : Int) (rowValue r ν) (rowValue (residueRow i m r) ν)

def ExactResidualOccurrences : Prop := ∀ (i m : Nat) (r : Row),
  (residueRow i m r).2 = r.2.filter (fun a => retained i a.2)

/-- Both active and inactive provenance cases are covered by the actual finite
source formula. Divisibility uses the actual common residue at a positive modulus. -/
def ActualMaximalTailAtom : Prop := ∀ (i : Nat) (a : Atom),
  PlainPhiDominance.isPlain a.row = true → ∀ ν : Nat → Nat,
    cutoff a ≤ ν i → (∀ b ∈ a.row.2, ν b.2.name ≤ ν i) →
      ((compileAtom i a).eval ν ↔ a.eval ν)

def LiteralTailLinearity : Prop := ∀ (i : Nat) (a : Atom),
  PlainPhiDominance.isPlain a.row = true → LinearRows.isLinear i (compileAtom i a) = true

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsTargets
