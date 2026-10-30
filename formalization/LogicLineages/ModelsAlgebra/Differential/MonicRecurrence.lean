module

public import LogicLineages.ModelsAlgebra.Differential.MonicRecurrenceTargets
public import LogicLineages.ModelsAlgebra.Differential.LinearOperator
public import LogicLineages.ModelsAlgebra.Differential.FiniteJet

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.MonicRecurrence

private theorem jet_eq_iterate {F : Type*} [Field F] [CharZero F]
    (D : Derivation ℚ F F) (a : F) (k : ℕ) :
    jet D a k = ((D : F → F)^[k]) a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [jet, ih, Function.iterate_succ_apply']

theorem operator_recurrence : Targets.monicOperatorRecurrence := by
  intro F _ _ D p a hp
  have heval : LinearOperator.applyOperator D p a =
      (∑ k : Fin p.natDegree, p.coeff k.val • FiniteJet.family D a p.natDegree k) +
        jet D a p.natDegree := by
    change (Polynomial.aeval D.toLinearMap p) a = _
    rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self p.natDegree)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.pow_apply]
    rw [Finset.sum_range_succ, hp.coeff_natDegree, one_smul]
    simp only [FiniteJet.family, jet_eq_iterate]
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => p.coeff k • ((D : F → F)^[k]) a) p.natDegree]
    rfl
  rw [heval]
  change _ + _ = 0 ↔ _ = ∑ k : Fin p.natDegree, -p.coeff k.val • _
  simp only [neg_smul, Finset.sum_neg_distrib]
  exact add_eq_zero_iff_eq_neg' 

theorem independent_solution_isomorphism : Targets.independentMonicSolutionIsomorphism := by
  intro F H _ _ _ _ D E p a b hp hn ha hb hia hib
  rw [LinearOperator.source_equation] at ha hb
  exact FiniteJet.independent_isomorphism F H D E a b p.natDegree
    (fun k => -p.coeff k.val) hn
    ((operator_recurrence F (integerDerivationToRat D) p a hp).mp ha)
    ((operator_recurrence H (integerDerivationToRat E) p b hp).mp hb) hia hib

end LogicLineages.ModelsAlgebra.Differential.MonicRecurrence
