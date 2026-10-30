module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWClosedAssignment
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import LogicLineages.OrdinalComparison.ActualCollapseBounds
public import LogicLineages.OrdinalComparison.EncodedFiniteBallsProof

@[expose] public section

/-! Original closed B-class supplier, independently authored after target
freeze. Positivity is derived from actual collapse domination and actual norm
additivity, not inserted into the grammar as a numerical-domain axiom. -/
namespace LogicLineages.ComputabilityKnowledge.WWClosedAssignmentProof

open LogicLineages.OrdinalComparison
open WWOrdinalTermSemantics WWClosedAssignment

private theorem sum_below (a b : Ordinal.{0}) (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalSum a b < epsilonZero := by
  obtain ⟨r, rfl⟩ := normalRepresentationComplete a ha
  obtain ⟨s, rfl⟩ := normalRepresentationComplete b hb
  rw [← naturalSumDenotation r s]
  exact normalRepresentationSound _

private theorem product_below (a b : Ordinal.{0}) (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalProduct a b < epsilonZero := by
  obtain ⟨r, rfl⟩ := normalRepresentationComplete a ha
  obtain ⟨s, rfl⟩ := normalRepresentationComplete b hb
  rw [← naturalProductDenotation r s]
  exact normalRepresentationSound _

private theorem omega_below : Ordinal.omega0 < epsilonZero := by
  have h : Ordinal.omega0 ^ ((1 : Nat) : Ordinal.{0}) < epsilonZero := (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr
    (WWOrdinalTermSemanticsProof.finiteNorm 1).1
  simpa only [Nat.cast_one, Ordinal.opow_one] using h

theorem originalOrdinalClosure : Comparators.WWClosedAssignment.OriginalOrdinalClosure := by
  intro ι ρ hρ t
  induction t with
  | var i => exact hρ i
  | zero => exact (WWOrdinalTermSemanticsProof.finiteNorm 0).1
  | one => simpa only [denote, Nat.cast_one] using (WWOrdinalTermSemanticsProof.finiteNorm 1).1
  | omega => exact omega_below
  | add a b ha hb => exact sum_below _ _ ha hb
  | emul a b ha hb =>
      have hpow : Ordinal.omega0 ^ denote ρ a < epsilonZero :=
        (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha
      have htwo : (2 : Ordinal.{0}) ≤ Ordinal.omega0 := (Ordinal.natCast_lt_omega0 2).le
      exact product_below _ _ ((Ordinal.opow_le_opow_left _ htwo).trans_lt hpow) hb
  | collapse a b ha hb => exact (WWOrdinalTermSemanticsProof.finiteNorm _).1

private theorem closed_below (t : Term Empty) : closedValue t < epsilonZero :=
  originalOrdinalClosure Empty Empty.elim (fun i => nomatch i) t

private theorem ground_value_aux (i : Nat) (t : Term Empty) (ht : B i t) :
    i = 0 → ∃ n : Nat, 0 < n ∧ closedValue t = (n : Ordinal.{0}) := by
  induction ht with
  | one i =>
      intro hi
      exact ⟨1, by omega, by simp [closedValue, denote]⟩
  | omega i hi => intro h; omega
  | @add i f g hf hg ihf ihg =>
      intro hi
      obtain ⟨n, hn, hfn⟩ := ihf hi
      obtain ⟨m, hm, hgm⟩ := ihg hi
      refine ⟨n + m, by omega, ?_⟩
      change ordinalNaturalSum (closedValue f) (closedValue g) = _
      rw [hfn, hgm, WWOrdinalTermSemanticsProof.naturalSum_finite]
  | @emul i f g hi hf hg ihf ihg => intro h; omega
  | @collapse f g hf hg hside ihf ihg =>
      intro hi
      obtain ⟨n, hn, hgn⟩ := ihg rfl
      let a := ordinalNaturalProduct Ordinal.omega0 (closedValue f)
      have ha : a < epsilonZero := product_below _ _ omega_below (closed_below f)
      have hg' := closed_below g
      have hd := actualCollapseDominatesNorm (ordinalNaturalSum a (closedValue g))
        (sum_below _ _ ha hg')
      rw [actualNaturalSumNormAdditive _ _ ha hg', hgn,
        (WWOrdinalTermSemanticsProof.finiteNorm n).2] at hd
      refine ⟨actualCollapse (ordinalNaturalSum a (closedValue g)), ?_, rfl⟩
      rw [hgn]
      omega
  | @lift i t hi ht iht => intro h; omega

theorem originalGroundValues : Comparators.WWClosedAssignment.OriginalGroundValues :=
  fun t ht => ground_value_aux 0 t ht rfl

theorem literalPositiveRepresentatives : Comparators.WWClosedAssignment.LiteralPositiveRepresentatives := by
  intro n
  induction n with
  | zero => exact ⟨B.one 0, by simp [positiveNumeral, closedValue, denote]⟩
  | succ n ih =>
      refine ⟨B.add ih.1 (B.one 0), ?_⟩
      change ordinalNaturalSum (closedValue (positiveNumeral n)) 1 = _
      rw [ih.2]
      simpa only [Nat.cast_one] using WWOrdinalTermSemanticsProof.naturalSum_finite (n + 1) 1

theorem singletonBoundedNorm : Comparators.WWClosedAssignment.SingletonBoundedNorm := by
  intro t i
  cases i with
  | zero => exact le_rfl
  | succ i =>
      have hz : actualOrdinalNorm (0 : Ordinal.{0}) = 0 := by
        simpa only [Nat.cast_zero] using (WWOrdinalTermSemanticsProof.finiteNorm 0).2
      change actualOrdinalNorm 0 ≤ actualOrdinalNorm (closedValue t)
      rw [hz]
      exact Nat.zero_le _

theorem exactFiniteExtraction : Comparators.WWClosedAssignment.ExactFiniteExtraction := by
  intro t ht
  obtain ⟨n, hn, htn⟩ := originalGroundValues t ht
  rw [htn]
  simp only [Ordinal.card_nat, Cardinal.toNat_natCast]
  exact ⟨hn, trivial, (WWOrdinalTermSemanticsProof.finiteNorm n).2⟩

theorem wwClosedAssignment : Comparators.WWClosedAssignment.Target :=
  ⟨originalOrdinalClosure, originalGroundValues, literalPositiveRepresentatives,
    singletonBoundedNorm, exactFiniteExtraction⟩

end LogicLineages.ComputabilityKnowledge.WWClosedAssignmentProof
