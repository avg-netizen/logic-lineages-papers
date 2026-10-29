module

public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions
public import LogicLineages.ModelsAlgebra.Differential.GeneratedField
public import LogicLineages.ModelsAlgebra.Differential.RationalBase
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Derivation.DifferentialRing

@[expose] public section

/-! Literal order-one constrainedness semantics from paper 15, def:constraint.
Existence and uniqueness up to designated-root differential isomorphism are
separate clauses. Neither divisibility nor nonconstancy is built into them.
The universe parameter ranges over arbitrary fields in Type u. ULift below
is the actual transported ordinary derivation, not a witness assumption. -/
namespace LogicLineages.ModelsAlgebra.Differential

universe u v w

instance liftedFieldCharZero {F : Type v} [Field F] [CharZero F] :
    CharZero (ULift.{u} F) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : F ≃+* ULift.{u} F).toRingHom)
    (ULift.ringEquiv.symm : F ≃+* ULift.{u} F).injective

noncomputable def liftOrdinaryDerivation {F : Type v} [Field F]
    (D : Derivation ℤ F F) : Derivation ℤ (ULift.{u} F) (ULift.{u} F) :=
  letI : Differential F := ⟨D⟩
  (Differential.equiv (ULift.ringEquiv : ULift.{u} F ≃+* F)).deriv

def HasDesignatedRootIso {F : Type v} {H : Type w}
    [Field F] [CharZero F] [Field H] [CharZero H]
    (D : Derivation ℤ F F) (E : Derivation ℤ H H) (a : F) (b : H) : Prop :=
  ∃ e : fieldGeneratedByJets (integerDerivationToRat D) a ≃ₐ[ℚ]
    fieldGeneratedByJets (integerDerivationToRat E) b,
    (e ⟨a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩ : H) = b ∧
    ∀ x, e (generatedFieldDerivation (integerDerivationToRat D) a x) =
      generatedFieldDerivation (integerDerivationToRat E) b (e x)

def ConstrainedOrderOne (p : BivariatePolynomial) (q : Polynomial ℚ) : Prop :=
  (∃ (F : Type u) (fieldF : Field F),
    letI : Field F := fieldF
    ∃ charF : CharZero F,
      letI : CharZero F := charF
      ∃ (D : Derivation ℤ F F) (a : F),
        pairEval a (D a) p = 0 ∧ Polynomial.aeval a q ≠ 0) ∧
  (∀ (F H : Type u) [Field F] [CharZero F] [Field H] [CharZero H]
    (D : Derivation ℤ F F) (E : Derivation ℤ H H) (a : F) (b : H),
    pairEval a (D a) p = 0 → Polynomial.aeval a q ≠ 0 →
    pairEval b (E b) p = 0 → Polynomial.aeval b q ≠ 0 →
    HasDesignatedRootIso D E a b)

end LogicLineages.ModelsAlgebra.Differential
