module
public import LogicLineages.StandardControlCurrent.InverseBoundaryBlockDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseBoundaryBlockTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open InverseBoundaryBlock HyperCloseBlock

def ActualBand : Prop := ∀ i a shift lower upper, 0 < a → ∀ ν,
  (DominantBoundary.region i a shift lower upper).eval ν →
  (DominantBoundary.center a lower).value ν - 2 ≤ ((ν i : Int)+shift).toNat ∧
  ((ν i : Int)+shift).toNat ≤ (DominantBoundary.center a lower).value ν + 2

def SingleElimination : Prop := ∀ i a shift lower upper p,
  0 < a → i ∉ lower.variables → i ∉ upper.variables → ∀ ν,
  (∃ n, (Matrix.conjunction (DominantBoundary.region i a shift lower upper) p).eval
    (Function.update ν i n)) ↔ (branch [] i a shift lower upper p).2.eval ν

def BlockElimination : Prop := ∀ (xs : List Nat) i a shift lower upper p,
  xs.Nodup → i ∈ xs → 0 < a → i ∉ lower.variables → i ∉ upper.variables → ∀ ν,
  existsNames xs (.conjunction (DominantBoundary.region i a shift lower upper) p) ν ↔
    existsNames (branch xs i a shift lower upper p).1 (branch xs i a shift lower upper p).2 ν

def ProgressSupport : Prop := ∀ (xs : List Nat) i a shift lower upper p,
  xs.Nodup → i ∈ xs → 0 < a → i ∉ lower.variables → i ∉ upper.variables →
  let b := branch xs i a shift lower upper p
  b.1.Nodup ∧ b.1.length+1=xs.length ∧ b.1.length<xs.length ∧
  i ∉ b.2.variables ∧
  ∀ j, j ∈ b.2.variables → j ∉ b.1 →
    j ∉ xs ∧ (j ∈ lower.variables ∨ j ∈ upper.variables ∨ j ∈ p.variables)

def LiteralCode : Prop := ∀ xs i a shift lower upper p,
  program (xs,i,a,shift,lower.encode,upper.encode,p.encode) =
    ((branch xs i a shift lower upper p).1,(branch xs i a shift lower upper p).2.encode)
def Programs : Prop := Computable program

def Full : Prop := ActualBand ∧ SingleElimination ∧ BlockElimination ∧ ProgressSupport ∧ LiteralCode ∧ Programs
end LogicLineages.StandardControlCurrent.InverseBoundaryBlockTargets
