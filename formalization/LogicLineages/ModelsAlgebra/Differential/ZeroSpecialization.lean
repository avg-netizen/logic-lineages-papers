module

public import LogicLineages.ModelsAlgebra.Differential.ZeroSpecializationTargets
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.ZeroSpecialization

open Polynomial

theorem zeroSpecializationTwoConstants : Targets.zeroSpecializationTwoConstants := by
  intro p q hp hq
  classical
  have hfinite := Polynomial.finite_setOf_isRoot hq
  obtain ⟨a, ha⟩ := hfinite.exists_notMem
  obtain ⟨b, hb⟩ := (hfinite.insert a).exists_notMem
  have hba : b ≠ a := fun h => hb (Set.mem_insert_iff.mpr (Or.inl h))
  have hbq : ¬q.IsRoot b := fun h => hb (Set.mem_insert_of_mem a h)
  have hsolution (c : ℚ) : pairEval c ((0 : Derivation ℤ ℚ ℚ) c) p = 0 := by
    change Polynomial.eval₂ (aeval c).toRingHom 0 p = 0
    rw [Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero, hp, map_zero]
  change q.eval a ≠ 0 at ha
  refine ⟨a, b, Ne.symm hba, hsolution a, hsolution b, ?_, ?_⟩
  · simpa only [IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using ha
  · simpa only [IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hbq

theorem distinctRationalRootsNotIsomorphic : Targets.distinctRationalRootsNotIsomorphic := by
  intro a b hab
  rintro ⟨e, he⟩
  apply hab
  have hc := e.commutes a
  have hv := congrArg Subtype.val hc
  have hroot : (algebraMap ℚ _ a) =
      (⟨a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩ :
        fieldGeneratedByJets (integerDerivationToRat (0 : Derivation ℤ ℚ ℚ)) a) := by
    apply Subtype.ext
    simp
  rw [hroot] at hv
  exact hv.symm.trans he

end LogicLineages.ModelsAlgebra.Differential.ZeroSpecialization
