module
public import LogicLineages.OrdinalComparison.PolynomialOrdinalProof
public import LogicLineages.OrdinalComparison.ConstantBudgetFactsProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem finiteOmegaPowerBelowEpsilonZero (d : Nat) :
    Ordinal.omega0 ^ (d : Ordinal) < epsilonZero := by
  have he := normalRepresentationSound (NONote.ofNat d)
  change (ONote.ofNat d).repr < epsilonZero at he
  rw [ONote.repr_ofNat] at he
  exact (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he

theorem polynomialRawNoteActualNorm (d : Nat) (a : Fin d → Nat) :
    actualOrdinalNorm (polynomialRawNote d a).repr = restrictedPartitionWeight a := by
  have hp := polynomialRawNoteNormalBoundNorm d a
  have hn := actualOrdinalNorm_notationCorrespondence (⟨polynomialRawNote d a, hp.1⟩ : NONote)
  change actualOrdinalNorm (polynomialRawNote d a).repr = Vendor.R1.treeWeight (polynomialRawNote d a) at hn
  exact hn.trans hp.2.2

theorem actualPolynomialNormPartitionCardinality : Targets.ActualPolynomialNormPartitionCardinality := by
  classical
  intro d b _
  let S := actualExactNormPredecessors (Ordinal.omega0 ^ (d : Ordinal)) b
  have hpow := finiteOmegaPowerBelowEpsilonZero d
  let encode : RestrictedPartitionState d b → {x : Ordinal // x ∈ S} := fun a =>
    ⟨(polynomialRawNote d a.1).repr,
      (actualExactNormPredecessorsMembership _ hpow b _).mpr
        ⟨(polynomialRawNoteNormalBoundNorm d a.1).2.1,
          (polynomialRawNoteActualNorm d a.1).trans a.2⟩⟩
  have hinj : Function.Injective encode := by
    intro a a' h
    have hr := congrArg Subtype.val h
    change (polynomialRawNote d a.1).repr = (polynomialRawNote d a'.1).repr at hr
    letI := (polynomialRawNoteNormalBoundNorm d a.1).1
    letI := (polynomialRawNoteNormalBoundNorm d a'.1).1
    have heq : polynomialRawNote d a.1 = polynomialRawNote d a'.1 := ONote.repr_inj.mp hr
    exact Subtype.ext (polynomialRawNoteInjective d heq)
  have hsurj : Function.Surjective encode := by
    intro x
    have hx := (actualExactNormPredecessorsMembership _ hpow b x.1).mp x.2
    obtain ⟨a, ha⟩ := polynomialRawNoteOrdinalComplete d x.1 hx.1
    have hw : restrictedPartitionWeight a = b := by
      have hn := polynomialRawNoteActualNorm d a
      rw [ha] at hn
      exact hn.symm.trans hx.2
    refine ⟨⟨a, hw⟩, ?_⟩
    apply Subtype.ext
    exact ha
  have hc := Nat.card_congr (Equiv.ofBijective encode ⟨hinj, hsurj⟩)
  have hS : Nat.card {x : Ordinal // x ∈ S} = S.card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  change S.card = Nat.card (RestrictedPartitionState d b)
  exact hS.symm.trans hc.symm

theorem fullActualPolynomialNormPartitionCardinality : Targets.FullActualPolynomialNormPartitionCardinality :=
  ⟨polynomialRawNoteNormalBoundNorm, polynomialRawNoteInjective,
    polynomialRawNoteOrdinalComplete, actualPolynomialNormPartitionCardinality⟩

end LogicLineages.OrdinalComparison
