module
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitTargets
public import LogicLineages.OrdinalComparison.WWOriginalOmegaProductProof
public import LogicLineages.OrdinalComparison.WWFixedShiftProof
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GeneralOmegaHeadLimit.Proof
open ForwardTranslation
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

private theorem head_le_sum (e : ONote) (c : ℕ+) (t b : ONote)
    (he : ONote.NF e) (hb : ONote.NF b) :
    Ordinal.omega0 ^ e.repr ≤ (rawNaturalSum (.oadd e c t) b).repr := by
  cases b with
  | zero => simpa only [rawNaturalSum] using ONote.omega0_le_oadd e c t
  | oadd f d u =>
    haveI : ONote.NF e := he
    haveI : ONote.NF f := hb.fst
    have hc := ONote.cmp_compares e f
    cases h : ONote.cmp e f with
    | lt =>
      have hef : e.repr < f.repr := by simpa only [h, Ordering.Compares, ONote.lt_def] using hc
      exact (Ordinal.opow_le_opow_right Ordinal.omega0_pos hef.le).trans
        (by simpa only [rawNaturalSum, h] using
          (ONote.omega0_le_oadd f d (rawNaturalSum (.oadd e c t) u)))
    | eq => simpa only [rawNaturalSum, h] using ONote.omega0_le_oadd e (c + d) (rawNaturalSum t u)
    | gt => simpa only [rawNaturalSum, h] using ONote.omega0_le_oadd e c (rawNaturalSum t (.oadd f d u))


private theorem one_sum_positive (e : ONote) (he : ONote.NF e) :
    0 < (rawNaturalSum 1 e).repr := by
  have h := head_le_sum .zero 1 .zero e ONote.NF.zero he
  change Ordinal.omega0 ^ 0 ≤ (rawNaturalSum 1 e).repr at h
  rw [Ordinal.opow_zero] at h
  exact (show (0 : Ordinal) < 1 from zero_lt_one).trans_le h

private theorem monomial_support : ∀ b : ONote, ONote.NF b →
    positiveSupport (rawMonomialProduct 1 1 b)
  | .zero, _ => True.intro
  | .oadd e c t, hb => by
    apply sum_support
    · exact ⟨one_sum_positive e hb.fst,True.intro⟩
    · exact monomial_support t hb.snd

theorem generalPositiveLimit : Targets.GeneralPositiveLimit := by
  intro a ha hae
  obtain ⟨y,hy⟩ := normalRepresentationComplete a hae
  let x : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have hx : x.1.repr = Ordinal.omega0 := by simp [x,ONote.repr]
  have hs : positiveSupport (rawNaturalProduct x.1 y.1) := by
    apply sum_support
    · exact monomial_support y.1 y.2
    · trivial
  have hd := naturalProductDenotation x y
  change (rawNaturalProduct x.1 y.1).repr = ordinalNaturalProduct x.1.repr y.1.repr at hd
  rw [hx,hy] at hd
  have hp : 0 < omegaHead a := Ordinal.omega0_pos.trans_le
    (OriginalDomain.actualOmegaNaturalProductInfinite a ha hae)
  refine ⟨hp,?_,?_⟩
  · rcases support_limit _ hs with hz | hl
    · have hz' : omegaHead a = 0 := hd.symm.trans hz
      rw [hz'] at hp
      exact False.elim (lt_irrefl _ hp)
    · change Order.IsSuccLimit (ordinalNaturalProduct Ordinal.omega0 a)
      rw [← hd]
      exact hl
  · have h := normalRepresentationSound (naturalProduct x y)
    change (rawNaturalProduct x.1 y.1).repr < epsilonZero at h
    change ordinalNaturalProduct Ordinal.omega0 a < epsilonZero
    rw [← hd]
    exact h

theorem actualClosedHeadCalibration : Targets.ActualClosedHeadCalibration := by
  intro a
  have he : (scalarHeadNote a).1.repr = fixedHead a := by
    rw [scalarHeadNote,naturalProductDenotation]
    simp [fixedHead,ONote.repr]
  have hl := generalPositiveLimit a.evaluate.1.repr (closedPositiveValuePositive a)
    (normalRepresentationSound a.evaluate)
  exact ⟨he,encodedClosedHeadCorrect a,hl⟩
end LogicLineages.OrdinalComparison.Source.GeneralOmegaHeadLimit.Proof
