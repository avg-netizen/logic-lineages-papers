module
public import LogicLineages.OrdinalComparison.ResidueRootCountTargets
public import LogicLineages.OrdinalComparison.ResidueFixednessPolynomialProof
public import LogicLineages.OrdinalComparison.ExponentialRootGapProof

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualResidueSmallExponentNonfixed : Targets.ActualResidueSmallExponentNonfixed.{u} := by
  intro K _ _ u s hu hs hsr z₀ hz₀
  classical
  by_contra h
  push_neg at h
  obtain ⟨he, heD, hc, hd⟩ := actualResidueFixednessPolynomialSize u s hu hs
  let P := (actualResidueFixednessPolynomial u s).map (algebraMap (ZMod 2) K)
  have hP : P ≠ 0 := by
    intro hp
    have hpc := congrArg (fun p : Polynomial K => p.coeff 0) hp
    simpa [P, Polynomial.coeff_map, hc] using hpc
  have hroots : (primitiveRoots (actualLinkedModulus u) K).val ⊆ P.roots := by
    intro z hz
    have hz' := isPrimitiveRoot_of_mem_primitiveRoots hz
    apply (Polynomial.mem_roots hP).mpr
    change P.eval z = 0
    simpa [P, Polynomial.eval_map] using
      actualResidueFixednessPolynomialRoot K u s hu hs z hz' (h z hz')
  have hcard := Polynomial.card_le_degree_of_subset_roots hroots
  rw [hz₀.card_primitiveRoots] at hcard
  have hdegree : P.natDegree = 2 ^ s * actualLinkedDegree u := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    dsimp only [P]
    rw [Polynomial.degree_map_eq_of_injective (algebraMap (ZMod 2) K).injective]
    exact hd
  rw [hdegree] at hcard
  have harith := actualLinkedResidueArithmetic u (by omega)
  have hgap := actualDiscreteRootCountGap (actualLinkedHalfExponent u) (actualLinkedDegree u)
    s harith.1 harith.2.1 hsr
  exact (Nat.not_lt_of_ge hcard) hgap

end LogicLineages.OrdinalComparison
