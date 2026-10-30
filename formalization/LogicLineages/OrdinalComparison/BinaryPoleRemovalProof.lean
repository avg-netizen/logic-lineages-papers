module
public import LogicLineages.OrdinalComparison.BinaryPoleRemovalTargets
public import LogicLineages.OrdinalComparison.BinaryPoleBudgetProof
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof
public import LogicLineages.OrdinalComparison.CartierProperProof
public import LogicLineages.OrdinalComparison.CartierSupportProof
public import LogicLineages.OrdinalComparison.PoleMultiplicityProof

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem fullActualBinaryHigherPoleRemoval : Targets.FullActualBinaryHigherPoleRemoval.{u} := by
  intro K _ _ _ _ d U hU
  let A := (actualBinarySourceDenominator d).map (algebraMap (ZMod 2) K)
  let f := actualBinaryRationalDifferential d U
  let μ := actualBinaryPoleBudget d
  let a := actualBinaryPoleTransient d
  have hc : A.coeff 0 = 1 := by
    rw [Polynomial.coeff_map, actualBinarySourceDenominatorConstant, map_one]
  have ha : A ≠ 0 := by intro h; simpa [h] using hc
  have hf : actualRationalProper f := by
    rw [actualRationalProperDegree K]
    by_cases hu : U = 0
    · left
      simp [f, actualBinaryRationalDifferential, hu]
    · right
      change (algebraMap (Polynomial K) (RatFunc K) U /
        algebraMap (Polynomial K) (RatFunc K) A).intDegree < 0
      rw [RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hu) (RatFunc.algebraMap_ne_zero ha),
        RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
      change U.degree < A.degree at hU
      rw [Polynomial.degree_eq_natDegree hu, Polynomial.degree_eq_natDegree ha] at hU
      have hnat : U.natDegree < A.natDegree := by exact_mod_cast hU
      omega
  refine ⟨actualDifferentialCartierIterateProper K f hf, ?_, ?_⟩
  · intro z n hn
    apply actualDifferentialCartierSupportContraction K z f μ a ?_ (Nat.le_pow_clog (by decide) μ) n hn
    intro m hm
    have hbound := actualBinarySourceRootMultiplicity K d z
    change A.rootMultiplicity z ≤ μ at hbound
    have hcast : (A.rootMultiplicity z : Int) ≤ (μ : Int) := by exact_mod_cast hbound
    exact actualMultiplicityPoleLowerSupport K A U ha z m (by omega)
  · intro z j
    change (actualTranslatedRationalEmbedding z
      ((actualDifferentialCartier (K := K))^[a + j] f)).coeff (-1) = _
    rw [Nat.add_comm a j, Function.iterate_add_apply]
    simpa using actualDifferentialCartierIteratedCoefficient K z
      ((actualDifferentialCartier (K := K))^[a] f) j (-1)

end LogicLineages.OrdinalComparison
