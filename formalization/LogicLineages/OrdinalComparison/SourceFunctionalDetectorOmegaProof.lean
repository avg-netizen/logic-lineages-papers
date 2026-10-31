module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorNumericProof
public import LogicLineages.OrdinalComparison.WWOriginalOmegaProductProof
public import LogicLineages.OrdinalComparison.WWOriginalProductLowerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain Vendor.R1

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


private theorem one_sum_positive (e : ONote) : 0 < (rawNaturalSum 1 e).repr := by
  have hw : 0 < treeWeight (rawNaturalSum 1 e) := by
    rw [rawNaturalSum_norm]
    change 0 < 1+treeWeight e
    omega
  cases h : rawNaturalSum 1 e with
  | zero => simp [h,treeWeight] at hw
  | oadd f c t => exact ONote.oadd_pos f c t

private theorem monomial_support : ∀ b : ONote, positiveSupport (rawMonomialProduct 1 1 b)
  | .zero => True.intro
  | .oadd e c t => by
    apply sum_support
    · exact ⟨one_sum_positive e,True.intro⟩
    · exact monomial_support t

private def omegaNote : NONote :=
  ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
private theorem omegaNote_repr : omegaNote.1.repr=Ordinal.omega0 := by
  simp [omegaNote,ONote.repr]

theorem omega_product_below (h : Ordinal) (he : h<epsilonZero) :
    ordinalNaturalProduct Ordinal.omega0 h<epsilonZero := by
  obtain ⟨y,hy⟩ := normalRepresentationComplete h he
  rw [← omegaNote_repr,← hy,← naturalProductDenotation]
  exact normalRepresentationSound _

theorem omega_product_norm (h : Ordinal) (he : h<epsilonZero) :
    actualOrdinalNorm (ordinalNaturalProduct Ordinal.omega0 h)≤2*actualOrdinalNorm h := by
  obtain ⟨y,hy⟩ := normalRepresentationComplete h he
  rw [← omegaNote_repr,← hy,← naturalProductDenotation,
    actualOrdinalNorm_notationCorrespondence (naturalProduct omegaNote y),
    actualOrdinalNorm_notationCorrespondence y]
  have hn := naturalProductNormBound omegaNote y
  simpa [omegaNote,treeWeight] using hn

theorem omega_product_limit (h : Ordinal) (hp : 0<h) (he : h<epsilonZero) :
    Order.IsSuccLimit (ordinalNaturalProduct Ordinal.omega0 h) := by
  obtain ⟨y,hy⟩ := normalRepresentationComplete h he
  have hs : positiveSupport (rawNaturalProduct omegaNote.1 y.1) := by
    apply sum_support
    · exact monomial_support y.1
    · trivial
  have hd := naturalProductDenotation omegaNote y
  change (rawNaturalProduct omegaNote.1 y.1).repr=ordinalNaturalProduct omegaNote.1.repr y.1.repr at hd
  rw [omegaNote_repr,hy] at hd
  rcases support_limit _ hs with hz | hl
  · have hi := actualOmegaNaturalProductInfinite h hp he
    rw [← hd,hz] at hi
    exact False.elim (not_le_of_gt Ordinal.omega0_pos hi)
  · rwa [hd] at hl

theorem app_head_domination (h k : Ordinal) (s t q : Nat)
    (hh : 0<h) (hk : 0<k) (he : h<epsilonZero) (ke : k<epsilonZero)
    (horder : ordinalNaturalProduct Ordinal.omega0 h<ordinalNaturalProduct Ordinal.omega0 k)
    (hn : actualOrdinalNorm h≤s) (hs : s≤q) (hq : 5≤q) :
    4*appValue h s q<appValue k t q := by
  exact head_domination _ _ s t q (omega_product_below h he) (omega_product_below k ke)
    (omega_product_limit h hh he) (omega_product_limit k hk ke) horder
    ((omega_product_norm h he).trans (Nat.mul_le_mul_left 2 hn)) hs hq
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
