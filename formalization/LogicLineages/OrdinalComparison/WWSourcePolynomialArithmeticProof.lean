module
public import LogicLineages.OrdinalComparison.WWSourcePolynomialArithmeticTargets
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem sourceOmegaPowerOmegaBelowEpsilon : Ordinal.omega0 ^ Ordinal.omega0 < epsilonZero := by
  let o : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have ho : Ordinal.omega0 < epsilonZero := by
    simpa [o, ONote.repr] using normalRepresentationSound o
  exact (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ho

theorem sourceNaturalSumPowerClosure : Targets.SourceNaturalSumPowerClosure := by
  intro a b k hae hbe ha hb
  obtain ⟨x, hx⟩ := normalRepresentationComplete a hae
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hbe
  rw [← hx] at ha
  rw [← hy] at hb
  rw [← hx, ← hy]
  rw [← naturalSumDenotation]
  exact (rawNaturalSum_below x.1 y.1 k
    (ONote.NF.below_of_lt' ha x.2) (ONote.NF.below_of_lt' hb y.2)).repr_lt

private theorem finite_sum (e f : ONote) (he : ONote.NF e) (hf : ONote.NF f)
    (helt : e.repr < Ordinal.omega0) (hflt : f.repr < Ordinal.omega0) :
    (rawNaturalSum e f).repr < Ordinal.omega0 := by
  obtain ⟨a, ha⟩ := Ordinal.lt_omega0.mp helt
  obtain ⟨b, hb⟩ := Ordinal.lt_omega0.mp hflt
  have hd := naturalSumDenotation (⟨e, he⟩ : NONote) (⟨f, hf⟩ : NONote)
  change (rawNaturalSum e f).repr = ordinalNaturalSum e.repr f.repr at hd
  rw [hd, ha, hb, naturalSum_finite]
  exact Ordinal.natCast_lt_omega0 _

private theorem monomial_below (e : ONote) (he : ONote.NF e)
    (helt : e.repr < Ordinal.omega0) (c : ℕ+) :
    ∀ b : ONote, ONote.NFBelow b Ordinal.omega0 →
      ONote.NFBelow (rawMonomialProduct e c b) Ordinal.omega0
  | .zero, _ => ONote.NFBelow.zero
  | .oadd f d u, hb => by
    apply rawNaturalSum_below
    · exact ONote.NFBelow.oadd (rawNaturalSum_normal e f he hb.fst)
        ONote.NFBelow.zero (finite_sum e f he hb.fst helt hb.lt)
    · exact monomial_below e he helt c u (hb.snd.mono hb.lt.le)

private theorem product_below : ∀ a : ONote, ONote.NFBelow a Ordinal.omega0 →
    ∀ b : ONote, ONote.NFBelow b Ordinal.omega0 →
      ONote.NFBelow (rawNaturalProduct a b) Ordinal.omega0
  | .zero, _, _, _ => ONote.NFBelow.zero
  | .oadd e c t, ha, b, hb => by
    apply rawNaturalSum_below
    · exact monomial_below e ha.fst ha.lt c b hb
    · exact product_below t (ha.snd.mono ha.lt.le) b hb

theorem sourceNaturalProductPolynomialClosure : Targets.SourceNaturalProductPolynomialClosure := by
  intro a b ha hb
  obtain ⟨x, hx⟩ := normalRepresentationComplete a (ha.trans sourceOmegaPowerOmegaBelowEpsilon)
  obtain ⟨y, hy⟩ := normalRepresentationComplete b (hb.trans sourceOmegaPowerOmegaBelowEpsilon)
  rw [← hx] at ha
  rw [← hy] at hb
  rw [← hx, ← hy]
  rw [← naturalProductDenotation]
  exact (product_below x.1 (ONote.NF.below_of_lt' ha x.2)
    y.1 (ONote.NF.below_of_lt' hb y.2)).repr_lt

theorem sourceBaseTwoLinearPolynomial : Targets.SourceBaseTwoLinearPolynomial := by
  intro a ha
  have htwo : (1 : Ordinal) < 2 := by exact_mod_cast (show (1 : Nat) < 2 by omega)
  have h := (Ordinal.opow_lt_opow_iff_right htwo).mpr ha
  have hsquare : Ordinal.omega0 ^ (2 : Ordinal) = Ordinal.omega0 * Ordinal.omega0 := by
    change Ordinal.omega0 ^ ((2 : Nat) : Ordinal) = _
    rw [Ordinal.opow_natCast, pow_two]
  rw [hsquare, Ordinal.opow_mul,
    Ordinal.opow_omega0 htwo (by simpa using Ordinal.natCast_lt_omega0 2)] at h
  exact h
end LogicLineages.OrdinalComparison
