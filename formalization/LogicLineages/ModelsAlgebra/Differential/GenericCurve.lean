module

public import LogicLineages.ModelsAlgebra.Differential.GenericCurveTargets
public import LogicLineages.ModelsAlgebra.Differential.FractionField
public import LogicLineages.ModelsAlgebra.Differential.AlgebraicExtension
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

/-! A concrete generic field is the actual AdjoinRoot quotient of the
Gauss-irreducible polynomial over Q(Y). Extend dY=1 and multiply the
extended derivation by the actual root z, obtaining Dy=z. The same field
and element avoid every nonzero rational polynomial simultaneously. -/

namespace LogicLineages.ModelsAlgebra.Differential.GenericCurve

open Polynomial

theorem genericCurveUniformWitness : Targets.genericCurveUniformWitness := by
  intro p hp hdegree hr
  let R := Polynomial ℚ
  let L := FractionRing R
  let P : Polynomial L := p.map (algebraMap R L)
  have hprim : p.IsPrimitive := hp.isPrimitive (Nat.ne_zero_of_lt hdegree)
  have hP : Irreducible P := hprim.irreducible_iff_irreducible_map_fraction_map.mp hp
  letI : Fact (Irreducible P) := ⟨hP⟩
  let F := AdjoinRoot P
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  letI : FiniteDimensional L F := (AdjoinRoot.powerBasis hP.ne_zero).finite
  letI : Algebra.IsAlgebraic L F := Algebra.IsAlgebraic.of_finite L F
  let z : F := AdjoinRoot.root P
  let x : L := algebraMap R L X
  let y : F := algebraMap L F x
  let inclusion : R →ₐ[ℚ] F :=
    (IsScalarTower.toAlgHom ℚ L F).comp (IsScalarTower.toAlgHom ℚ R L)
  have heval (q : Polynomial ℚ) : aeval y q = inclusion q := by
    change aeval (inclusion X) q = inclusion q
    rw [Polynomial.aeval_algHom_apply]
    exact congrArg inclusion (Polynomial.aeval_X_left_apply q)
  have hinj : Function.Injective inclusion :=
    (algebraMap L F).injective.comp (IsFractionRing.injective R L)
  have hy : Transcendental ℚ y := by
    rw [transcendental_iff_injective]
    intro q r h
    apply hinj
    simpa only [← heval] using h
  have hcoeff : (algebraMap L F).comp (algebraMap R L) = (aeval y).toRingHom := by
    apply RingHom.ext
    intro q
    exact (heval q).symm
  have hroot : pairEval y z p = 0 := by
    have hz : aeval z P = 0 := by
      change Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P) P = 0
      exact AdjoinRoot.eval₂_root P
    change Polynomial.eval₂ (aeval y).toRingHom z p = 0
    change Polynomial.eval₂ (algebraMap L F) z (p.map (algebraMap R L)) = 0 at hz
    rw [Polynomial.eval₂_map, hcoeff] at hz
    exact hz
  have hz : z ≠ 0 := by
    intro hz
    have hc : aeval y (p.eval 0) = 0 := by
      simpa [pairEval, hz, ← Polynomial.coeff_zero_eq_eval_zero] using hroot
    exact hr ((transcendental_iff.mp hy) _ hc)
  letI : Module ℚ L := Algebra.toModule
  letI : Module R L := Algebra.toModule
  let dR : Derivation ℚ R L := Polynomial.mkDerivation ℚ (1 : L)
  obtain ⟨dL, hdL, _⟩ :=
    FractionField.fractionFieldDerivationExtension ℚ R L dR
  have hdx : dL x = 1 := by
    rw [hdL]
    exact Polynomial.mkDerivation_X ℚ (1 : L)
  letI : Algebra ℤ L := Ring.toIntAlgebra L
  letI : Module ℤ L := AddCommGroup.toIntModule L
  letI : Algebra ℤ F := Ring.toIntAlgebra F
  obtain ⟨dF, hdF, _⟩ :=
    AlgebraicExtension.algebraicDerivationExtension L F (dL.restrictScalars ℤ)
  have hdy : dF y = 1 := by
    rw [hdF]
    change algebraMap L F (dL x) = 1
    rw [hdx, map_one]
  let D : Derivation ℤ F F := z • dF
  have hDy : D y = z := by
    change z • dF y = z
    rw [hdy, smul_eq_mul, mul_one]
  refine ⟨F, inferInstance, inferInstance, D, y, hy, ?_, ?_, ?_⟩
  · rwa [hDy]
  · rwa [hDy]
  · intro q hq hzero
    exact hq ((transcendental_iff.mp hy) q hzero)

theorem genericCurveAvoidance : Targets.genericCurveAvoidance := by
  intro p hp hdegree hr q hq
  obtain ⟨F, fieldF, charF, D, a, ha, hDa, hpa, hav⟩ :=
    genericCurveUniformWitness p hp hdegree hr
  letI : Field F := fieldF
  letI : CharZero F := charF
  exact ⟨F, fieldF, charF, D, a, hDa, hpa, hav q hq⟩

end LogicLineages.ModelsAlgebra.Differential.GenericCurve
