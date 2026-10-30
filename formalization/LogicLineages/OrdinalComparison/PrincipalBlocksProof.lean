module
public import LogicLineages.OrdinalComparison.PrincipalBlocksTargets
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm
public import Mathlib.Data.List.Pairwise

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem blocks_repr (o : ONote) :
    ((principalExponentBlocks o).map fun e => Ordinal.omega0 ^ e.repr).sum = o.repr := by
  induction o with
  | zero => simp [principalExponentBlocks, ONote.repr]
  | oadd e n tail _ ih =>
    simp only [principalExponentBlocks, List.map_append, List.map_replicate,
      List.sum_append, List.sum_replicate, Ordinal.nsmul_eq_mul, ih, ONote.repr]

private theorem blocks_weight (o : ONote) :
    principalBlocksWeight (principalExponentBlocks o) = Vendor.R1.treeWeight o := by
  induction o with
  | zero => rfl
  | oadd e n tail _ ih =>
    simp only [principalExponentBlocks, principalBlocksWeight, List.map_append,
      List.map_replicate, List.sum_append, List.sum_replicate, nsmul_eq_mul] at ih ⊢
    rw [ih]
    rfl

theorem actualPrincipalBlocksDenotation : Targets.ActualPrincipalBlocksDenotation := by
  intro o ho
  refine ⟨blocks_repr o, ?_⟩
  rw [blocks_weight]
  exact (actualOrdinalNorm_notationCorrespondence ⟨o, ho⟩).symm

private theorem blocks_below (o : ONote) : ∀ b : Ordinal, ONote.NFBelow o b →
    ∀ e ∈ principalExponentBlocks o, e.repr < b := by
  induction o with
  | zero => simp [principalExponentBlocks]
  | oadd d n tail _ ih =>
    intro b hb e he
    rcases List.mem_append.mp he with he | he
    · have hed := List.eq_of_mem_replicate he
      subst e
      exact hb.lt
    · exact (ih d.repr hb.snd e he).trans hb.lt

theorem actualPrincipalBlocksNormalOrder : Targets.ActualPrincipalBlocksNormalOrder := by
  intro o
  induction o with
  | zero => intro _; simp [principalExponentBlocks]
  | oadd e n tail _ ih =>
    intro ho
    have ht := ih ho.snd
    constructor
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · have hde := List.eq_of_mem_replicate hd
        subst d
        exact ho.fst
      · exact ht.1 d hd
    · change (List.replicate n.val e ++ principalExponentBlocks tail).Pairwise _
      apply List.pairwise_append.mpr
      refine ⟨List.pairwise_replicate.mpr (Or.inr le_rfl), ht.2, ?_⟩
      intro d hd f hf
      have hde := List.eq_of_mem_replicate hd
      subst d
      exact (blocks_below tail e.repr ho.snd' f hf).le

private theorem blocks_positive (o : ONote) : ONote.NF o → Ordinal.omega0 ∣ o.repr →
    ∀ e ∈ principalExponentBlocks o, 0 < e.repr := by
  induction o with
  | zero => simp [principalExponentBlocks]
  | oadd d n tail _ ih =>
    intro ho hdiv e he
    have hd := ho.of_dvd_omega0 hdiv
    rcases List.mem_append.mp he with he | he
    · have hed := List.eq_of_mem_replicate he
      subst e
      exact pos_iff_ne_zero.mpr hd.1
    · exact ih ho.snd hd.2 e he

theorem actualPrincipalBlocksLimitDomain : Targets.ActualPrincipalBlocksLimitDomain := by
  intro o ho hl
  constructor
  · intro hz
    have hp := hl.bot_lt
    rw [← blocks_repr o, hz] at hp
    simpa using hp
  · exact blocks_positive o ho (Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hl.isSuccPrelimit)

end LogicLineages.OrdinalComparison
