module

public import LogicLineages.ModelsAlgebra.Differential.ConstrainedDefinitions
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section

/-! The actual finite jet field from paper 15 lem:genericjets. A recurrence
is a literal equation between derivatives with rational coefficients; neither
field closure nor an isomorphism is included in its definition. -/
namespace LogicLineages.ModelsAlgebra.Differential.FiniteJet

variable {F : Type*} [Field F] [CharZero F]

def family (D : Derivation ℚ F F) (a : F) (n : ℕ) : Fin n → F :=
  fun k => jet D a k.val

def field (D : Derivation ℚ F F) (a : F) (n : ℕ) : IntermediateField ℚ F :=
  IntermediateField.adjoin ℚ (Set.range (family D a n))

def Recurrence (D : Derivation ℚ F F) (a : F) (n : ℕ) (c : Fin n → ℚ) : Prop :=
  jet D a n = ∑ k : Fin n, c k • family D a n k

end LogicLineages.ModelsAlgebra.Differential.FiniteJet
