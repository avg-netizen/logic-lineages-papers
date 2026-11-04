module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowDefinitions
public import Mathlib.Computability.Primrec.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowTargets

/-- Source p50 caseII6: every guarded coefficient-close pair has either a
bounded original left variable, a bounded original right variable, or equal
actual signed hyper-indices. These are actual computed bounds, not fields. -/
def ActualCollisionAlternatives : Prop :=
  ∀ (i j : Nat) (e h k l : Int) (c : Nat) (ν : Nat → Nat),
    (HyperWindow.closeMatrix i j e h k l c).eval ν →
      ν i < HyperWindow.leftBound e h l ∨
      ν j < HyperWindow.rightBound h k l c ∨
      (HyperWindow.indexTerm i e).value ν = (HyperWindow.indexTerm j k).value ν

/-- A complete arbitrary-matrix TWO-variable elimination clause. Every branch
has only one of the two original existential quantifiers; all other variables
and dependent occurrences stay under the same original valuation. -/
def ActualTwoVariableElimination : Prop :=
  ∀ (i j : Nat), i ≠ j → ∀ (e h k l : Int) (c : Nat) (p : Matrix) (ν : Nat → Nat),
    (∃ x y : Nat,
      (HyperWindow.closeMatrix i j e h k l c).eval
        (Function.update (Function.update ν i x) j y) ∧
      p.eval (Function.update (Function.update ν i x) j y)) ↔
    (∃ y : Nat, (HyperWindow.leftCases i j e h k l c p).eval (Function.update ν j y)) ∨
    (∃ x : Nat, (HyperWindow.rightCases i j e h k l c p).eval (Function.update ν i x)) ∨
    (∃ y : Nat, (HyperWindow.equalCases i j e h k l c p).eval (Function.update ν j y))

def ExactSupportReduction : Prop :=
  ∀ (i j : Nat), i ≠ j → ∀ (e h k l : Int) (c : Nat) (p : Matrix) (v : Nat),
    (v ∈ (HyperWindow.leftCases i j e h k l c p).variables →
      v ≠ i ∧ (v = j ∨ v ∈ p.variables)) ∧
    (v ∈ (HyperWindow.rightCases i j e h k l c p).variables →
      v ≠ j ∧ (v = i ∨ v ∈ p.variables)) ∧
    (v ∈ (HyperWindow.equalCases i j e h k l c p).variables →
      v ≠ i ∧ (v = j ∨ v ∈ p.variables))

/-- The displayed enumeration bounds are actual uniform numerical programs. -/
def ActualBoundPrograms : Prop :=
  Primrec (fun p : Int × (Int × Int) => HyperWindow.leftBound p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Int × (Int × (Int × Nat)) =>
    HyperWindow.rightBound p.1 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowTargets
