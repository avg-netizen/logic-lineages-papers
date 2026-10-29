module

public import LogicLineages.ModelsAlgebra.Differential.AlgebraicExtensionTargets
public import Mathlib.FieldTheory.Differential.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

@[expose] public section

/-! Glue the actually constructed finite-extension derivations along finite
intermediate fields. Coherence uses the proved separable algebra-homomorphism
chain rule, including for uniqueness into an arbitrary proposed extension. -/

namespace LogicLineages.ModelsAlgebra.Differential.AlgebraicExtension

open IntermediateField

section Construction

variable (F K : Type*) [Field F] [CharZero F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K] [_root_.Differential F]

noncomputable instance singletonFinite (x : K) : FiniteDimensional F F⟮x⟯ :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)

noncomputable def value (x : K) : K :=
  ((_root_.Differential.deriv (R := F⟮x⟯) (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯)) : K)

theorem value_eq_finite (S : IntermediateField F K) [FiniteDimensional F S]
    (x : S) : value F K (x : K) = (_root_.Differential.deriv (R := S) x : K) := by
  let h : F⟮(x : K)⟯ ≤ S := adjoin_simple_le_iff.mpr x.property
  have hder := _root_.Differential.algHom_deriv'
    (IntermediateField.inclusion h) (IntermediateField.inclusion_injective h)
    (⟨(x : K), mem_adjoin_simple_self F (x : K)⟩ : F⟮(x : K)⟯)
  exact congrArg (fun y : S => (y : K)) hder

theorem value_algebraMap (x : F) :
    value F K (algebraMap F K x) = algebraMap F K (_root_.Differential.deriv x) := by
  let S : IntermediateField F K := ⊥
  have h := value_eq_finite F K S (algebraMap F S x)
  rw [DifferentialAlgebra.deriv_algebraMap] at h
  exact h

theorem value_zero : value F K 0 = 0 := by
  simpa using value_algebraMap F K (0 : F)

theorem value_one : value F K 1 = 0 := by
  simpa using value_algebraMap F K (1 : F)

theorem value_add (x y : K) : value F K (x + y) = value F K x + value F K y := by
  let S : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  let a : S := ⟨x, (show F⟮x⟯ ≤ S from le_sup_left) (mem_adjoin_simple_self F x)⟩
  let b : S := ⟨y, (show F⟮y⟯ ≤ S from le_sup_right) (mem_adjoin_simple_self F y)⟩
  have h := value_eq_finite F K S (a + b)
  rw [map_add] at h
  change value F K (x + y) =
    (_root_.Differential.deriv (R := S) a : K) +
    (_root_.Differential.deriv (R := S) b : K) at h
  rw [← value_eq_finite F K S a, ← value_eq_finite F K S b] at h
  exact h

theorem value_mul (x y : K) :
    value F K (x * y) = x * value F K y + y * value F K x := by
  let S : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  let a : S := ⟨x, (show F⟮x⟯ ≤ S from le_sup_left) (mem_adjoin_simple_self F x)⟩
  let b : S := ⟨y, (show F⟮y⟯ ≤ S from le_sup_right) (mem_adjoin_simple_self F y)⟩
  have h := value_eq_finite F K S (a * b)
  rw [_root_.Differential.deriv.leibniz] at h
  change value F K (x * y) =
    x * (_root_.Differential.deriv (R := S) b : K) +
    y * (_root_.Differential.deriv (R := S) a : K) at h
  rw [← value_eq_finite F K S a, ← value_eq_finite F K S b] at h
  exact h

noncomputable def extension : Derivation ℤ K K where
  toLinearMap :=
    ({ toFun := value F K
       map_zero' := value_zero F K
       map_add' := value_add F K } : K →+ K).toIntLinearMap
  map_one_eq_zero' := value_one F K
  leibniz' := by
    intro x y
    exact value_mul F K x y

theorem extension_algebraMap (x : F) :
    extension F K (algebraMap F K x) = algebraMap F K (_root_.Differential.deriv x) :=
  value_algebraMap F K x

theorem extension_unique (E : Derivation ℤ K K)
    (hE : ∀ x, E (algebraMap F K x) = algebraMap F K (_root_.Differential.deriv x)) :
    E = extension F K := by
  letI : _root_.Differential K := ⟨E⟩
  letI : DifferentialAlgebra F K := ⟨hE⟩
  ext x
  have h := _root_.Differential.algHom_deriv'
    (F⟮x⟯.val) (F⟮x⟯.val.injective)
    (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯)
  exact h.symm

end Construction

theorem algebraicDerivationExtension : Targets.algebraicDerivationExtension := by
  intro F K _ _ _ _ _ D
  letI : _root_.Differential F := ⟨D⟩
  exact ⟨extension F K, extension_algebraMap F K, extension_unique F K⟩

theorem algebraicClosureDerivationExtension : Targets.algebraicClosureDerivationExtension := by
  intro F _ _ D
  exact algebraicDerivationExtension F (AlgebraicClosure F) D

end LogicLineages.ModelsAlgebra.Differential.AlgebraicExtension
