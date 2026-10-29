module

public import LogicLineages.ModelsAlgebra.Differential.FractionFieldTargets
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Localization.Basic

@[expose] public section

/-! Encode a fraction-field-valued derivation by its square-zero graph,
localize this genuine algebra map, then recover the derivative from its
second coordinate. Uniqueness is localization extensionality of graphs. -/

namespace LogicLineages.ModelsAlgebra.Differential.FractionField

section Graph

variable {K R F : Type*} [Field K] [CommRing R] [Field F]
  [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]

def graph (D : Derivation K R F) : R →ₐ[K] TrivSqZeroExt F F where
  toFun r := (algebraMap R F r, D r)
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' := by
    intro x y
    apply TrivSqZeroExt.ext <;> simp [map_add]
  map_mul' := by
    intro x y
    apply TrivSqZeroExt.ext
    · simp
    · simpa only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_mk, op_smul_eq_smul, Algebra.smul_def,
        Algebra.algebraMap_self_apply] using D.leibniz x y
  commutes' := by
    intro k
    apply TrivSqZeroExt.ext
    · exact (IsScalarTower.algebraMap_apply K R F k).symm
    · exact D.map_algebraMap k

@[simp] theorem graph_fst (D : Derivation K R F) (r : R) :
    (graph D r).fst = algebraMap R F r := rfl

@[simp] theorem graph_snd (D : Derivation K R F) (r : R) :
    (graph D r).snd = D r := rfl

end Graph

section Localization

variable {K R F : Type*} [Field K] [CommRing R] [IsDomain R] [Field F]
  [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
  [IsFractionRing R F]

theorem graph_denominator_unit (D : Derivation K R F) (r : nonZeroDivisors R) :
    IsUnit (graph D (r : R)) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  exact IsLocalization.map_units F r

noncomputable def liftedGraph (D : Derivation K R F) : F →ₐ[K] TrivSqZeroExt F F :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors R) (graph_denominator_unit D)

@[simp] theorem liftedGraph_algebraMap (D : Derivation K R F) (r : R) :
    liftedGraph D (algebraMap R F r) = graph D r :=
  IsLocalization.lift_eq (graph_denominator_unit D) r

theorem liftedGraph_fst (D : Derivation K R F) (x : F) :
    (liftedGraph D x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K F F).toRingHom.comp (liftedGraph D).toRingHom =
      RingHom.id F := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    simp
  exact RingHom.congr_fun h x

noncomputable def extension (D : Derivation K R F) : Derivation K F F where
  toLinearMap :=
    { toFun := fun x => (liftedGraph D x).snd
      map_add' := by
        intro x y
        simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := by
        intro k x
        simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
  map_one_eq_zero' := by
    change (liftedGraph D 1).snd = 0
    simp only [map_one, TrivSqZeroExt.snd_one]
  leibniz' := by
    intro x y
    change (liftedGraph D (x * y)).snd =
      x • (liftedGraph D y).snd + y • (liftedGraph D x).snd
    simp only [map_mul, TrivSqZeroExt.snd_mul, liftedGraph_fst,
      op_smul_eq_smul]

@[simp] theorem extension_algebraMap (D : Derivation K R F) (r : R) :
    extension D (algebraMap R F r) = D r := by
  change (liftedGraph D (algebraMap R F r)).snd = D r
  rw [liftedGraph_algebraMap, graph_snd]

theorem extension_unique (D : Derivation K R F) (E : Derivation K F F)
    (hE : ∀ r, E (algebraMap R F r) = D r) : E = extension D := by
  have h : (graph E).toRingHom = (liftedGraph D).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro r
    apply TrivSqZeroExt.ext
    · simp
    · simp [hE]
  ext x
  exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun h x)

end Localization

theorem fractionFieldDerivationExtension : Targets.fractionFieldDerivationExtension := by
  intro K R F _ _ _ _ _ _ _ _ _ D
  exact ⟨extension D, extension_algebraMap D, extension_unique D⟩

theorem constructedFractionFieldDerivationExtension :
    Targets.constructedFractionFieldDerivationExtension := by
  intro K R _ _ _ _ D
  exact fractionFieldDerivationExtension K R (FractionRing R) D

end LogicLineages.ModelsAlgebra.Differential.FractionField
