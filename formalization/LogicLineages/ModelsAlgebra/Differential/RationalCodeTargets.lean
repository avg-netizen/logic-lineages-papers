module

public import LogicLineages.ModelsAlgebra.Differential.RationalCodeDefinitions

@[expose] public section

/-! Exact arithmetic suppliers for paper 15 cor:algorithmone. These targets
precede their proofs. They supply explicit coded field arithmetic and tests,
not yet polynomial division, radical calculation, or the decision corollary.
-/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

open RationalCode

def rationalCodeCoverage : Prop := ∀ q : ℚ, ∃ c : Code, value c = q

def rationalCodeCorrect : Prop :=
  value zero = 0 ∧ value one = 1 ∧
  (∀ a b, value (add a b) = value a + value b) ∧
  (∀ a, value (neg a) = -value a) ∧
  (∀ a b, value (mul a b) = value a * value b) ∧
  (∀ a, value (inverse a) = (value a)⁻¹) ∧
  (∀ a b, value (div a b) = value a / value b) ∧
  (∀ a, isZero a = true ↔ value a = 0) ∧
  (∀ a b, equal a b = true ↔ value a = value b)

def rationalCodePrimitiveRecursive : Prop :=
  Primrec₂ add ∧ Primrec neg ∧ Primrec₂ mul ∧ Primrec inverse ∧
  Primrec₂ div ∧ Primrec isZero ∧ Primrec₂ equal

def rationalCodeRoundtrip : Prop :=
  ∀ c : Code, (@Encodable.decode Code _ (Encodable.encode c)) = some c

end LogicLineages.ModelsAlgebra.Differential.Targets
