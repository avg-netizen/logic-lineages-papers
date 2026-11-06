module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
import LogicLineages.OrdinalComparison.PrincipalBlocksProof
import LogicLineages.OrdinalComparison.FiniteCollapse
import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadSourceProof

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

private theorem word_member (es : List ONote) : ∀ c : Nat, ∀ p ∈ principalKernelWord es c,
    p.1 ∈ es := by
  induction es with
  | nil => intro c p hp; cases hp
  | cons e es ih =>
      intro c p hp
      change p ∈ principalKernelWord es (c+(1+Vendor.R1.treeWeight e)) ++ [(e,c)] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact List.mem_cons_of_mem e (ih _ p hp)
      · have heq : p = (e,c) := List.mem_singleton.mp hp
        subst p
        exact List.mem_cons_self

private theorem member_weight (es : List ONote) : ∀ e ∈ es,
    Vendor.R1.treeWeight e ≤ principalBlocksWeight es := by
  induction es with
  | nil => intro e he; cases he
  | cons a es ih =>
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        change Vendor.R1.treeWeight a ≤ (1+Vendor.R1.treeWeight a) + principalBlocksWeight es
        omega
      · have h := ih e he
        change Vendor.R1.treeWeight e ≤ (1+Vendor.R1.treeWeight a) + principalBlocksWeight es
        omega

private theorem finite_note (e : ONote) (he : ONote.NF e) (hb : e.repr < Ordinal.omega0) :
    e = ONote.ofNat (Vendor.R1.treeWeight e) := by
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hb
  haveI : ONote.NF e := he
  have heq : e = ONote.ofNat n := by
    apply ONote.repr_inj.mp
    simpa only [ONote.repr_ofNat] using hn
  have hw : Vendor.R1.treeWeight e = n := by
    rw [heq]
    exact norm_ofNat n
  simpa only [hw] using heq

theorem polynomialCalls : Targets.PolynomialCalls := by
  intro o hlimit hpoly p hp
  have hmem := word_member (principalExponentBlocks o.1) 0 p hp
  have hn := (actualPrincipalBlocksNormalOrder o.1 o.2).1 p.1 hmem
  have hb := blocks_below o.1 Ordinal.omega0 (ONote.NF.below_of_lt' hpoly o.2) p.1 hmem
  have heq := finite_note p.1 hn hb
  have hpositive := (actualPrincipalBlocksLimitDomain o.1 o.2 hlimit).2 p.1 hmem
  have hrepr : p.1.repr = (Vendor.R1.treeWeight p.1 : Ordinal) :=
    (congrArg ONote.repr heq).trans (ONote.repr_ofNat _)
  rw [hrepr] at hpositive
  have hnat : 0 < Vendor.R1.treeWeight p.1 := by exact_mod_cast hpositive
  have hweight := member_weight (principalExponentBlocks o.1) p.1 hmem
  have hsum : principalBlocksWeight (principalExponentBlocks o.1) = Vendor.R1.treeWeight o.1 :=
    (actualPrincipalBlocksDenotation o.1 o.2).2.trans (actualOrdinalNorm_notationCorrespondence o)
  rw [hsum] at hweight
  exact ⟨hnat, heq, hweight⟩

private theorem polynomial_below_epsilon :
    Ordinal.omega0 ^ Ordinal.omega0 < epsilonZero := by
  let o : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have ho : Ordinal.omega0 < epsilonZero := by
    simpa [o, ONote.repr] using normalRepresentationSound o
  exact (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ho

theorem polynomialHeadCoverage : Targets.PolynomialHeadCoverage := by
  intro lam hlimit hpoly
  obtain ⟨o, ho⟩ := normalRepresentationComplete lam (hpoly.trans polynomial_below_epsilon)
  refine ⟨o, ho, ?_⟩
  unfold ValidHead
  rw [rawNoteDecodeEncode]
  refine ⟨o.2, ?_, ?_⟩
  · simpa only [ho] using hlimit
  · simpa only [ho] using hpoly

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadSourceProof
