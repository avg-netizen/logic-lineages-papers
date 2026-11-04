module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BinomialTargets
open Dioph DiophantinePolynomialBridge

/-- The ordinary binomial theorem interpreted in the actual base-u digits.
No coefficient bounds or nonzero n assumptions are needed for this identity. -/
def BinomialDigitReconstruction : Prop := ∀ (n u : Nat),
  Nat.ofDigits u ((List.range (n+1)).map (Nat.choose n)) = (u+1)^n

/-- Actual digit extraction, including indices beyond the end of the list. -/
def NaturalDigitExtraction : Prop := ∀ (u : Nat) (digits : List Nat) (k : Nat),
  0 < u → (∀ a ∈ digits, a < u) →
  (Nat.ofDigits u digits / u^k) % u = digits.getD k 0

/-- All n,k, including n=0 and k>n; u may vary with the input. -/
def BinomialDigitExtraction : Prop := ∀ (n k u : Nat),
  2^n < u → Nat.choose n k = ((u+1)^n / u^k) % u

/-- The full nonnegative binomial function, reusing the paid power graph. -/
def BinomialDiophantine : Prop := ∀ (alpha : Type) (f g : (alpha → Nat) → Nat),
  DiophFn f → DiophFn g → DiophFn (fun v => Nat.choose (f v) (g v))

def BinomialPolynomialRepresentation : Prop :=
  ∃ (m : Nat) (p : PolynomialCircuit.Code),
    CodeRepresents {v : Fin 3 → Nat | Nat.choose (v 0) (v 1) = v 2} m p

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BinomialTargets
