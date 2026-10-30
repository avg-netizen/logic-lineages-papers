module

public import LogicLineages.ModelsAlgebra.Differential.IsomorphismJetTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.IsomorphismJet

variable {F H : Type*} [Field F] [CharZero F] [Field H] [CharZero H]

private def containedJet (D : Derivation ℤ F F) (a : F) (k : ℕ) :
    fieldGeneratedByJets (integerDerivationToRat D) a :=
  ⟨jet (integerDerivationToRat D) a k, IntermediateField.subset_adjoin ℚ _ ⟨k, rfl⟩⟩

theorem preserves_jet_relations : Targets.designatedRootIsoPreservesJetRelations := by
  intro F H _ _ _ _ D E a b hiso n q
  obtain ⟨e, he, hcompat⟩ := hiso
  have hj (k : ℕ) : e (containedJet D a k) = containedJet E b k := by
    induction k with
    | zero =>
      apply Subtype.ext
      exact he
    | succ k ih =>
      change e (generatedFieldDerivation (integerDerivationToRat D) a (containedJet D a k)) =
        generatedFieldDerivation (integerDerivationToRat E) b (containedJet E b k)
      rw [hcompat, ih]
  let va (k : Fin n) := containedJet D a k.val
  let vb (k : Fin n) := containedJet E b k.val
  have hmap : e.toAlgHom.comp (MvPolynomial.aeval va) = MvPolynomial.aeval vb := by
    apply MvPolynomial.algHom_ext
    intro k
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgEquiv.coe_algHom, va, vb] using hj k.val
  have hA : ((MvPolynomial.aeval va) q : F) =
      MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a n) q := by
    exact MvPolynomial.comp_aeval_apply va (fieldGeneratedByJets (integerDerivationToRat D) a).val q
  have hB : ((MvPolynomial.aeval vb) q : H) =
      MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat E) b n) q := by
    exact MvPolynomial.comp_aeval_apply vb (fieldGeneratedByJets (integerDerivationToRat E) b).val q
  have hmap' : e ((MvPolynomial.aeval va) q) = (MvPolynomial.aeval vb) q :=
    AlgHom.congr_fun hmap q
  constructor
  · intro hzero
    have ha : (MvPolynomial.aeval va) q = 0 := by
      apply Subtype.ext
      exact hA.trans hzero
    have hb : (MvPolynomial.aeval vb) q = 0 := by rw [← hmap', ha, map_zero]
    exact hB.symm.trans (congrArg Subtype.val hb)
  · intro hzero
    have hb : (MvPolynomial.aeval vb) q = 0 := by
      apply Subtype.ext
      exact hB.trans hzero
    have ha : (MvPolynomial.aeval va) q = 0 := by
      apply e.injective
      rw [map_zero, hmap', hb]
    exact hA.symm.trans (congrArg Subtype.val ha)

end LogicLineages.ModelsAlgebra.Differential.IsomorphismJet
