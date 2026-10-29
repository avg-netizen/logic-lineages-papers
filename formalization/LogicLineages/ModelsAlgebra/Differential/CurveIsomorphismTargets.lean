module

public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions
public import LogicLineages.ModelsAlgebra.Differential.GeneratedField
public import LogicLineages.ModelsAlgebra.Differential.RationalBase
public import Mathlib.Algebra.Algebra.Equiv

@[expose] public section

/-! Full designated-root differential-field isomorphism comparator for
paper 15 `lem:curve`, paper.tex lines 130–157. Both actual fields generated
by all jets occur in the type, as do their constructed restricted
derivations. No common-field isomorphism, finite-jet identification,
separant nonvanishing, or derivation-compatibility supplier is assumed.
The rational-base interpretation of an ordinary derivation was constructed
and checked previously. Written before the external isomorphism candidate.
This theorem alone does not provide the generic witness or constraint criteria. -/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def curveDesignatedRootIsomorphism : Prop :=
  ∀ (F : Type u) (H : Type v) [Field F] [CharZero F] [Field H] [CharZero H]
    (D : Derivation ℤ F F) (E : Derivation ℤ H H)
    (p : BivariatePolynomial) (a : F) (b : H),
    Irreducible p → 0 < p.natDegree → D a ≠ 0 → E b ≠ 0 →
    pairEval a (D a) p = 0 → pairEval b (E b) p = 0 →
    ∃ e : fieldGeneratedByJets (integerDerivationToRat D) a ≃ₐ[ℚ]
      fieldGeneratedByJets (integerDerivationToRat E) b,
      (e ⟨a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩ : H) = b ∧
      ∀ x, e (generatedFieldDerivation (integerDerivationToRat D) a x) =
        generatedFieldDerivation (integerDerivationToRat E) b (e x)

end LogicLineages.ModelsAlgebra.Differential.Targets
