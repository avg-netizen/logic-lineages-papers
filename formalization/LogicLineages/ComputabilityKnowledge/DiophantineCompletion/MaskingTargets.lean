module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BinomialTargets
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Bitwise

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingTargets
open Dioph

/-- The exact actual binary mask is the parity of a variable binomial
coefficient. All natural inputs, including a>b and either zero, are retained. -/
def BitMaskParity : Prop := ∀ (a b : Nat),
  (Nat.choose b a) % 2 = 1 ↔ a &&& b = a

def BitMaskDiophantine : Prop := ∀ (alpha : Type) (f g : (alpha → Nat) → Nat),
  DiophFn f → DiophFn g → Dioph {v | f v &&& g v = f v}

/-- The ordinary arithmetic-and-mask characterization of actual Nat AND.
Natural subtraction has its original meaning; no new convention is imposed. -/
def BitAndCharacterization : Prop := ∀ (a b c : Nat),
  a &&& b = c ↔ c &&& a = c ∧ a &&& (a+b-c) = a

def BitAndDiophantine : Prop := ∀ (alpha : Type) (f g : (alpha → Nat) → Nat),
  DiophFn f → DiophFn g → DiophFn (fun v => f v &&& g v)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingTargets
