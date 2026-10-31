module
public import LogicLineages.OrdinalComparison.WWSourcePolynomialIndexTargets
public import LogicLineages.OrdinalComparison.WWSourcePolynomialArithmeticProof
public import LogicLineages.OrdinalComparison.WWOriginalOmegaProductProof
@[expose] public section
namespace LogicLineages.OrdinalComparison
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private def positiveSupport : ONote → Prop
  | .zero => True
  | .oadd e _ t => 0 < e.repr ∧ positiveSupport t

private theorem sum_support : ∀ a b : ONote,
    positiveSupport a → positiveSupport b → positiveSupport (rawNaturalSum a b)
  | .zero, b, _, hb => by simpa only [rawNaturalSum] using hb
  | a, .zero, ha, _ => by cases a <;> simpa only [rawNaturalSum] using ha
  | .oadd e c t, .oadd f d u, ha, hb => by
    cases h : ONote.cmp e f with
    | lt =>
      rw [rawNaturalSum, h]
      exact ⟨hb.1, sum_support (.oadd e c t) u ha hb.2⟩
    | eq =>
      rw [rawNaturalSum, h]
      exact ⟨ha.1, sum_support t u ha.2 hb.2⟩
    | gt =>
      rw [rawNaturalSum, h]
      exact ⟨ha.1, sum_support t (.oadd f d u) ha.2 hb⟩
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; simp only [sizeOf, ONote._sizeOf_1]; omega

private theorem support_limit (a : ONote) (ha : positiveSupport a) :
    a.repr = 0 ∨ Order.IsSuccLimit a.repr := by
  induction a with
  | zero => exact Or.inl rfl
  | oadd e c t ihe iht =>
    have hm : Order.IsSuccLimit (Ordinal.omega0 ^ e.repr * ((c : Nat) : Ordinal)) :=
      Ordinal.isSuccLimit_mul_left
        (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 ha.1.ne')
        (by exact_mod_cast c.pos)
    rcases iht ha.2 with hz | hl
    · right
      simpa only [ONote.repr, hz, add_zero] using hm
    · exact Or.inr (Ordinal.isSuccLimit_add _ hl)

private theorem one_sum_positive (e : ONote) (he : ONote.NF e)
    (hb : e.repr < Ordinal.omega0) : 0 < (rawNaturalSum 1 e).repr := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hb
  have hd := naturalSumDenotation (⟨1, ONote.nf_one⟩ : NONote) (⟨e, he⟩ : NONote)
  change (rawNaturalSum 1 e).repr = ordinalNaturalSum (1 : ONote).repr e.repr at hd
  rw [hd, ONote.repr_one, hn]
  have h := naturalSum_finite 1 n
  rw [h]
  exact_mod_cast (show 0 < 1 + n by omega)

private theorem monomial_support : ∀ b : ONote, ONote.NFBelow b Ordinal.omega0 →
    positiveSupport (rawMonomialProduct 1 1 b)
  | .zero, _ => True.intro
  | .oadd e c t, hb => by
    apply sum_support
    · exact ⟨one_sum_positive e hb.fst hb.lt, True.intro⟩
    · exact monomial_support t (hb.snd.mono hb.lt.le)

theorem sourcePolynomialIndexLimit : Targets.SourcePolynomialIndexLimit := by
  intro a ha hb
  have hae := hb.trans sourceOmegaPowerOmegaBelowEpsilon
  have homega : Ordinal.omega0 < Ordinal.omega0 ^ Ordinal.omega0 := by
    simpa only [Ordinal.opow_one] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr Ordinal.one_lt_omega0
  refine ⟨?_, sourceNaturalProductPolynomialClosure _ _ homega hb⟩
  obtain ⟨y, hy⟩ := normalRepresentationComplete a hae
  let x : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have hx : x.1.repr = Ordinal.omega0 := by simp [x, ONote.repr]
  have hs : positiveSupport (rawNaturalProduct x.1 y.1) := by
    apply sum_support
    · exact monomial_support y.1 (ONote.NF.below_of_lt' (by rw [hy]; exact hb) y.2)
    · trivial
  have hd := naturalProductDenotation x y
  change (rawNaturalProduct x.1 y.1).repr = ordinalNaturalProduct x.1.repr y.1.repr at hd
  rw [hx, hy] at hd
  rcases support_limit _ hs with hz | hl
  · have hi := Source.OriginalDomain.actualOmegaNaturalProductInfinite a ha hae
    rw [← hd, hz] at hi
    exact False.elim (not_le_of_gt Ordinal.omega0_pos hi)
  · rwa [hd] at hl
end LogicLineages.OrdinalComparison
