module

public import LogicLineages.ModelsAlgebra.Differential.FiniteJetTargets
public import LogicLineages.ModelsAlgebra.Differential.CurveIsomorphism
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.FiniteJet

open scoped IntermediateField.algebraAdjoinAdjoin

variable {F H : Type*} [Field F] [CharZero F] [Field H] [CharZero H]

private theorem generator_mem (D : Derivation ℚ F F) (a : F) (n : ℕ) (k : Fin n) :
    family D a n k ∈ field D a n :=
  IntermediateField.subset_adjoin ℚ _ ⟨k, rfl⟩

private theorem recurrence_mem (D : Derivation ℚ F F) (a : F) (n : ℕ)
    (c : Fin n → ℚ) (hc : Recurrence D a n c) : jet D a n ∈ field D a n := by
  rw [hc]
  apply sum_mem
  intro k _
  rw [Algebra.smul_def]
  exact (field D a n).mul_mem ((field D a n).algebraMap_mem (c k))
    (generator_mem D a n k)

theorem closed_and_equals_generated : Targets.finiteJetClosedAndEqualsGenerated := by
  intro F _ _ D a n c hn hc
  have hclosed : IsDerivationClosed D (field D a n) := by
    apply adjoin_isDerivationClosed
    rintro x ⟨k, rfl⟩
    change jet D a (k.val + 1) ∈ field D a n
    by_cases hk : k.val + 1 < n
    · exact generator_mem D a n ⟨k.val + 1, hk⟩
    · have hkn : k.val + 1 = n := by omega
      rw [hkn]
      exact recurrence_mem D a n c hc
  refine ⟨hclosed, le_antisymm ?_ ?_⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨k, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _ ⟨k.val, rfl⟩
  · apply fieldGeneratedByJets_le D a _ _ hclosed
    exact generator_mem D a n ⟨0, hn⟩

private noncomputable def familyFieldEquiv {ι : Type*} (x : ι → F) (y : ι → H)
    (hx : AlgebraicIndependent ℚ x) (hy : AlgebraicIndependent ℚ y) :
    IntermediateField.adjoin ℚ (Set.range x) ≃ₐ[ℚ]
      IntermediateField.adjoin ℚ (Set.range y) :=
  IsFractionRing.algEquivOfAlgEquiv (hx.aevalEquiv.symm.trans hy.aevalEquiv)

private theorem familyFieldEquiv_gen {ι : Type*} (x : ι → F) (y : ι → H)
    (hx : AlgebraicIndependent ℚ x) (hy : AlgebraicIndependent ℚ y) (i : ι) :
    familyFieldEquiv x y hx hy ⟨x i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩ =
      ⟨y i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩ := by
  have hX : algebraMap (Algebra.adjoin ℚ (Set.range x))
      (IntermediateField.adjoin ℚ (Set.range x)) (hx.aevalEquiv (MvPolynomial.X i)) =
      ⟨x i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩ := by
    apply Subtype.ext
    simpa using hx.algebraMap_aevalEquiv (MvPolynomial.X i)
  rw [← hX]
  simp only [familyFieldEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  apply Subtype.ext
  simpa using hy.algebraMap_aevalEquiv (MvPolynomial.X i)

theorem independent_isomorphism : Targets.independentFiniteJetIsomorphism := by
  intro F H _ _ _ _ D E a b n c hn hca hcb hia hib
  let d := integerDerivationToRat D
  let e := integerDerivationToRat E
  obtain ⟨hclosedA, hfieldA⟩ := closed_and_equals_generated F d a n c hn hca
  obtain ⟨hclosedB, hfieldB⟩ := closed_and_equals_generated H e b n c hn hcb
  let A := field d a n
  let B := field e b n
  let va (k : Fin n) : A := ⟨family d a n k, generator_mem d a n k⟩
  let vb (k : Fin n) : B := ⟨family e b n k, generator_mem e b n k⟩
  let dA := restrictDerivation d A hclosedA
  let dB := restrictDerivation e B hclosedB
  let iso : A ≃ₐ[ℚ] B := familyFieldEquiv (family d a n) (family e b n) hia hib
  have hiso (k : Fin n) : iso (va k) = vb k :=
    familyFieldEquiv_gen (family d a n) (family e b n) hia hib k
  have hnextA (k : Fin n) (hk : k.val + 1 < n) : dA (va k) = va ⟨k.val + 1, hk⟩ := by
    apply Subtype.ext
    rfl
  have hnextB (k : Fin n) (hk : k.val + 1 < n) : dB (vb k) = vb ⟨k.val + 1, hk⟩ := by
    apply Subtype.ext
    rfl
  have hlastA (k : Fin n) (hk : k.val + 1 = n) : dA (va k) = ∑ j, c j • va j := by
    apply Subtype.ext
    change jet d a (k.val + 1) = _
    rw [hk, hca]
    simp [va, family, d]
  have hlastB (k : Fin n) (hk : k.val + 1 = n) : dB (vb k) = ∑ j, c j • vb j := by
    apply Subtype.ext
    change jet e b (k.val + 1) = _
    rw [hk, hcb]
    simp [vb, family, e]
  have hcompat : ∀ x, iso (dA x) = dB (iso x) := by
    apply CurveIsomorphism.compatible_on_adjoin (Set.range (family d a n)) dA dB iso.toAlgHom
    rintro x ⟨k, rfl⟩
    change iso (dA (va k)) = dB (iso (va k))
    rw [hiso]
    by_cases hk : k.val + 1 < n
    · rw [hnextA k hk, hnextB k hk, hiso]
    · have hkn : k.val + 1 = n := by omega
      rw [hlastA k hkn, hlastB k hkn, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hiso j]
      exact iso.toLinearEquiv.map_smul (c j) (va j)
  let u := IntermediateField.equivOfEq hfieldA.symm
  let v := IntermediateField.equivOfEq hfieldB
  let result := (u.trans iso).trans v
  refine ⟨result, ?_, ?_⟩
  · change (v (iso (u ⟨a, _⟩)) : H) = b
    have hu : u ⟨a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩ = va ⟨0, hn⟩ := by
      apply Subtype.ext
      rfl
    rw [hu, hiso]
    rfl
  · intro x
    have hu : u (generatedFieldDerivation d a x) = dA (u x) := by
      apply Subtype.ext
      rfl
    have hv (y : B) : v (dB y) = generatedFieldDerivation e b (v y) := by
      apply Subtype.ext
      rfl
    change v (iso (u (generatedFieldDerivation d a x))) = _
    rw [hu, hcompat, hv]
    rfl

end LogicLineages.ModelsAlgebra.Differential.FiniteJet
