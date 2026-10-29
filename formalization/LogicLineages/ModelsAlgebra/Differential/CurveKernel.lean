module

public import LogicLineages.ModelsAlgebra.Differential.CurveTargets
public import LogicLineages.ModelsAlgebra.Differential.RationalBase
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Algebraic.Basic

@[expose] public section

/-! Gauss irreducibility over Q(Y), evaluation into the ambient field, and
contraction of arbitrary polynomial multiples prove the actual curve kernel.
Primitivity of the test polynomial is never assumed. -/

namespace LogicLineages.ModelsAlgebra.Differential.CurveKernel

open Polynomial

/-- Contract arbitrary polynomial divisibility by a primitive polynomial.
Unlike a convenient symmetric Gauss lemma, q need not be primitive. -/
theorem primitive_dvd_of_fraction_dvd {R L : Type*} [CommRing R] [IsDomain R]
    [Nonempty (NormalizedGCDMonoid R)] [Field L] [Algebra R L] [IsFractionRing R L]
    {p q : Polynomial R} (hp : p.IsPrimitive)
    (h : p.map (algebraMap R L) ∣ q.map (algebraMap R L)) : p ∣ q := by
  obtain ⟨g, hg⟩ := h
  have hprod : p.map (algebraMap R L) * g ∈ Polynomial.lifts (algebraMap R L) := by
    rw [← hg]
    exact Polynomial.mem_lifts _ |>.mpr ⟨q, rfl⟩
  obtain ⟨r, hr⟩ := (Polynomial.mem_lifts g).mp (hp.map_mul_mem_lifts_iff.mp hprod)
  refine ⟨r, ?_⟩
  apply Polynomial.map_injective _ (IsFractionRing.injective R L)
  rw [Polynomial.map_mul, hr]
  exact hg

/-- An irreducible polynomial with a root generates the kernel of any
field-valued polynomial evaluation. The proof evaluates a Bezout identity. -/
theorem irreducible_eval_kernel {L F : Type*} [Field L] [Field F]
    (e : Polynomial L →+* F) {p : Polynomial L} (hp : Irreducible p) (hp0 : e p = 0)
    (q : Polynomial L) (hq0 : e q = 0) : p ∣ q := by
  apply hp.dvd_iff_not_isCoprime.mpr
  rintro ⟨u, v, huv⟩
  have h := congrArg e huv
  have hz : (0 : F) = 1 := by simpa [hp0, hq0] using h
  exact zero_ne_one hz

theorem curveEvaluationKernel : Targets.curveEvaluationKernel := by
  intro F _ _ p a b hp hdegree ha hp0 q
  let L := FractionRing (Polynomial ℚ)
  let φ : L →+* F := IsFractionRing.lift (transcendental_iff_injective.mp ha)
  let e : Polynomial L →+* F := Polynomial.eval₂RingHom φ b
  have hcomp : φ.comp (algebraMap (Polynomial ℚ) L) = (Polynomial.aeval a).toRingHom := by
    apply RingHom.ext
    intro r
    exact IsFractionRing.lift_algebraMap (transcendental_iff_injective.mp ha) r
  have heval (r : BivariatePolynomial) :
      e (r.map (algebraMap (Polynomial ℚ) L)) = pairEval a b r := by
    change Polynomial.eval₂ φ b (r.map (algebraMap (Polynomial ℚ) L)) =
      Polynomial.eval₂ (Polynomial.aeval a).toRingHom b r
    rw [Polynomial.eval₂_map, hcomp]
  have hprimitive : p.IsPrimitive := hp.isPrimitive (Nat.ne_zero_of_lt hdegree)
  have hirr : Irreducible (p.map (algebraMap (Polynomial ℚ) L)) :=
    hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hp
  constructor
  · intro hq
    apply primitive_dvd_of_fraction_dvd (L := L) hprimitive
    apply irreducible_eval_kernel e hirr
    · rw [heval, hp0]
    · rw [heval, hq]
  · rintro ⟨r, rfl⟩
    rw [map_mul, hp0, zero_mul]

theorem curveSeparantNonzero : Targets.curveSeparantNonzero := by
  intro F _ _ p a b hp hdegree ha hp0 hsep
  have hdvd : p ∣ p.derivative :=
    (curveEvaluationKernel F p a b hp hdegree ha hp0 (separant p)).mp hsep
  have hne : p.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (Nat.ne_zero_of_lt hdegree)
  exact (not_dvd_of_natDegree_lt hne
    (Polynomial.natDegree_derivative_lt (Nat.ne_zero_of_lt hdegree))) hdvd

theorem ordinaryCurveKernelAndSeparant : Targets.ordinaryCurveKernelAndSeparant := by
  intro F _ _ D p a hp hdegree hDa hp0
  have ha : Transcendental ℚ a := by
    intro halg
    exact hDa (integerDerivation_eq_zero_of_isAlgebraic D halg)
  exact ⟨curveEvaluationKernel F p a (D a) hp hdegree ha hp0,
    curveSeparantNonzero F p a (D a) hp hdegree ha hp0⟩

end LogicLineages.ModelsAlgebra.Differential.CurveKernel
