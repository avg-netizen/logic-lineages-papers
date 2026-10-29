module

public import Mathlib.FieldTheory.Differential.Basic

@[expose] public section

/-!
# Extending an actual ordinary derivation

The finite-dimensional extension is constructed by Mathlib's proved
primitive-element/minimal-polynomial construction. Its existence and
uniqueness are not supplied as hypotheses or new project axioms.
-/

namespace LogicLineages.ModelsAlgebra.Differential

variable {F : Type*} {K : Type*} [Field F] [CharZero F] [Field K]
variable [Algebra F K] [FiniteDimensional F K]

theorem existsUnique_finite_derivation_extension (D : Derivation ℤ F F) :
    ∃! E : Derivation ℤ K K,
      ∀ x, E (algebraMap F K x) = algebraMap F K (D x) := by
  letI : _root_.Differential F := ⟨D⟩
  letI : _root_.Differential K :=
    _root_.Differential.differentialFiniteDimensional F K
  letI : DifferentialAlgebra F K :=
    _root_.Differential.differentialAlgebraFiniteDimensional
  refine ⟨_root_.Differential.deriv, ?_, ?_⟩
  · intro x
    exact DifferentialAlgebra.deriv_algebraMap x
  · intro E hE
    let original : {_a : _root_.Differential K // DifferentialAlgebra F K} :=
      ⟨inferInstance, inferInstance⟩
    let alternative : {_a : _root_.Differential K // DifferentialAlgebra F K} := by
      letI : _root_.Differential K := ⟨E⟩
      exact ⟨inferInstance, ⟨hE⟩⟩
    letI : Unique {_a : _root_.Differential K // DifferentialAlgebra F K} :=
      _root_.Differential.uniqueDifferentialAlgebraFiniteDimensional
    have h := Subsingleton.elim alternative original
    exact congrArg (fun e => e.val.deriv) h

end LogicLineages.ModelsAlgebra.Differential
