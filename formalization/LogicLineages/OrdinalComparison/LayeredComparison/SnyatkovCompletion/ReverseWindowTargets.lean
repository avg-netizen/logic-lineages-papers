module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowTargets

def ActualMinusWitness : Prop :=
  ∀ (i : Nat) (anchor : Term) (e : Int) (c : Nat) (ν : Nat → Nat),
    (ReverseWindow.closeMatrix i anchor e c).eval ν →
      ∃ d : Nat, d ≤ c ∧
        anchor.value ν = (shiftTerm (.variable i) e).value ν + d ∧
        (ReverseWindow.replacementTerm anchor e d).value ν = ν i

/-- Actual sourceII5 multivariable elimination with the minus-oriented window.
Arbitrary anchor syntax omits only the eliminated original name. The complete
matrix and every original signed guard are retained under one shared ν. -/
def ActualFiniteElimination : Prop :=
  ∀ (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix),
    i ∉ anchor.variables → ∀ ν : Nat → Nat,
      (∃ n : Nat, (ReverseWindow.closeMatrix i anchor e c).eval (Function.update ν i n) ∧
        p.eval (Function.update ν i n)) ↔
      (ReverseWindow.finiteCases i anchor e c p).eval ν

def ExactSupportReduction : Prop :=
  ∀ (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix),
    i ∉ anchor.variables → ∀ v : Nat,
      v ∈ (ReverseWindow.finiteCases i anchor e c p).variables →
        v ≠ i ∧ (v ∈ anchor.variables ∨ v ∈ p.variables)

def LiteralCodeCalibration : Prop :=
  ∀ (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix),
    ReverseWindow.Code.finiteCases (ReverseWindow.Code.input i anchor.encode e c p.encode) =
      (ReverseWindow.finiteCases i anchor e c p).encode

def ActualCodeComputation : Prop := Computable ReverseWindow.Code.finiteCases

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowTargets
