module

public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions
public import LogicLineages.ModelsAlgebra.Differential.GeneratedFieldDefinitions
public import LogicLineages.ModelsAlgebra.Differential.RationalBase
public import Mathlib.Algebra.Algebra.Equiv

@[expose] public section

/-! Independent exact targets for paper 15's r=0 case, lines 205–209.
The actual zero ordinary derivation on Q supplies two distinct rational
solutions avoiding q. No irreducibility is needed for this stronger
supplier. A designated-root Q-algebra equivalence of their actual all-jet
fields is impossible; hence a differential one is impossible too.
Written before proof; this does not itself define or decide constrainedness. -/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

def zeroSpecializationTwoConstants : Prop :=
  ∀ (p : BivariatePolynomial) (q : Polynomial ℚ), p.eval 0 = 0 → q ≠ 0 →
    ∃ a b : ℚ, a ≠ b ∧
      pairEval a ((0 : Derivation ℤ ℚ ℚ) a) p = 0 ∧
      pairEval b ((0 : Derivation ℤ ℚ ℚ) b) p = 0 ∧
      Polynomial.aeval a q ≠ 0 ∧ Polynomial.aeval b q ≠ 0

def distinctRationalRootsNotIsomorphic : Prop :=
  ∀ a b : ℚ, a ≠ b →
    ¬∃ e : fieldGeneratedByJets (integerDerivationToRat (0 : Derivation ℤ ℚ ℚ)) a ≃ₐ[ℚ]
      fieldGeneratedByJets (integerDerivationToRat (0 : Derivation ℤ ℚ ℚ)) b,
      (e ⟨a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩ : ℚ) = b

end LogicLineages.ModelsAlgebra.Differential.Targets
