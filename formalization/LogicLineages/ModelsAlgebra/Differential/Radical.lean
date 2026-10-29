module

public import LogicLineages.ModelsAlgebra.Differential.RadicalTargets
public import LogicLineages.ModelsAlgebra.Differential.CurveKernel
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Radical

open Polynomial UniqueFactorizationMonoid

theorem rationalRadicalMonicSquarefree : Targets.rationalRadicalMonicSquarefree := by
  intro r hr
  refine ⟨Polynomial.monic_normalize radical_ne_zero, ?_⟩
  exact (normalize_associated (radical r)).squarefree_iff.mpr squarefree_radical

theorem radicalAmbientRootVanishing : Targets.radicalAmbientRootVanishing := by
  intro F _ _ r q c hr hd hroot
  have hc : IsAlgebraic ℚ c := ⟨r, hr, hroot⟩
  have hm : Irreducible (minpoly ℚ c) := minpoly.irreducible hc.isIntegral
  have hmr : minpoly ℚ c ∣ r := minpoly.dvd ℚ c hroot
  have hrad : minpoly ℚ c ∣ radical r :=
    (dvd_radical_iff_of_irreducible hm hr).mpr hmr
  have hnorm : minpoly ℚ c ∣ rationalRadical r := dvd_normalize_iff.mpr hrad
  exact (minpoly.dvd_iff.mp (hnorm.trans hd))

theorem rationalRadicalRootCriterion : Targets.rationalRadicalRootCriterion := by
  intro r q hr
  constructor
  · intro hd c hc
    exact radicalAmbientRootVanishing (AlgebraicClosure ℚ) r q c hr hd hc
  · intro hall
    change normalize (radical r) ∣ q
    apply normalize_dvd_iff.mpr
    unfold radical
    apply Finset.prod_dvd_of_isRelPrime
    · exact pairwise_primeFactors_isRelPrime
    · intro f hf
      have hfacts := (Polynomial.mem_normalizedFactors_iff hr).mp (mem_primeFactors.mp hf)
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure ℚ) f
        (ne_of_gt hfacts.1.degree_pos)
      have hrc : aeval c r = 0 := by
        obtain ⟨s, rfl⟩ := hfacts.2.2
        rw [map_mul, hc, zero_mul]
      exact CurveKernel.irreducible_eval_kernel (aeval c).toRingHom hfacts.1 hc q (hall c hrc)

theorem badConstantCurveWitness : Targets.badConstantCurveWitness := by
  intro p q hr hnot
  have hn : ¬∀ c : AlgebraicClosure ℚ, aeval c (p.eval 0) = 0 → aeval c q = 0 :=
    fun h => hnot ((rationalRadicalRootCriterion (p.eval 0) q hr).mpr h)
  classical
  push_neg at hn
  obtain ⟨c, hc, hq⟩ := hn
  refine ⟨c, ?_, hq⟩
  simpa [pairEval, ← Polynomial.coeff_zero_eq_eval_zero] using hc

end LogicLineages.ModelsAlgebra.Differential.Radical
