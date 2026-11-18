module
public import LogicLineages.ControlSensitivityCurrent.GenericScalarTargets
public import LogicLineages.ControlSensitivityCurrent.CompositeEraserProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseRecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.GenericScalar
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open ParametricSourceSuccessor
open OriginalDomain
private theorem sum_below {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalSum a b < epsilonZero := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalSumDenotation x y]
  exact normalRepresentationSound (naturalSum x y)

private theorem product_below {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalProduct a b < epsilonZero := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalProductDenotation x y]
  exact normalRepresentationSound (naturalProduct x y)

private theorem omega_below : Ordinal.omega0 < epsilonZero := by
  have h := (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr
    (show (1 : Ordinal) < epsilonZero by simpa using (finiteNorm 1).1)
  simpa only [Ordinal.opow_one, epsilonZero] using h

private theorem two_power_below {a : Ordinal} (ha : a < epsilonZero) :
    (2 : Ordinal) ^ a < epsilonZero := by
  have hω : Ordinal.omega0 ^ a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha
  exact (Ordinal.opow_le_opow_left a
    (show (2 : Ordinal) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 2).le)).trans_lt hω

private theorem positive_of_norm {a : Ordinal} (h : 0 < actualOrdinalNorm a) : 0 < a := by
  by_contra hn
  have ha : a = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hz : actualOrdinalNorm 0 = 0 := by simpa using (finiteNorm 0).2
  rw [ha, hz] at h
  omega

private theorem sum_positive {a b : Ordinal} (ha : 0 < a)
    (hae : a < epsilonZero) (hbe : b < epsilonZero) : 0 < ordinalNaturalSum a b := by
  apply positive_of_norm
  rw [actualNaturalSumNormAdditivity a b hae hbe]
  have := actualPositiveOrdinalNorm a ha hae
  omega

private theorem product_positive {a b : Ordinal} (ha : 0 < a) (hb : 0 < b)
    (hae : a < epsilonZero) (hbe : b < epsilonZero) : 0 < ordinalNaturalProduct a b := by
  apply positive_of_norm
  have h := actualNaturalProductNormLower a b ha hb hae hbe
  have hna := actualPositiveOrdinalNorm a ha hae
  have hnb := actualPositiveOrdinalNorm b hb hbe
  omega


theorem belowEpsilon : GenericScalarTargets.BelowEpsilon := by
  intro f Γ ρ t
  induction t with
  | var c => exact (finiteNorm _).1
  | zero => exact zero_lt_epsilonZero
  | one => simpa only [denoteWith, Nat.cast_one] using (finiteNorm 1).1
  | omega => exact omega_below
  | add a b ha hb => exact sum_below ha hb
  | emul a b ha hb => exact product_below (two_power_below ha) hb
  | collapse a b ha hb => exact (finiteNorm _).1

private theorem collapse_pos (f : Nat → Nat) (a b : Ordinal)
    (ha : a < epsilonZero) (hb : b < epsilonZero) (hp : 0 < b) :
    0 < (ParametricActualCollapse.collapseWith f
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b) : Ordinal) := by
  have hh := product_below omega_below ha
  have he := sum_below hh hb
  have hs : 0 < ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b := by
    apply positive_of_norm
    rw [actualNaturalSumNormAdditivity _ _ hh hb]
    have := actualPositiveOrdinalNorm b hp hb
    omega
  have hz : actualOrdinalNorm (0 : Ordinal) = 0 := by simpa using (finiteNorm 0).2
  have h := (ParametricActualCollapse.Proof.equation f _ he).1 0 hs (by rw [hz]; omega)
  have hn : 0 < ParametricActualCollapse.collapseWith f
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b) := by omega
  exact_mod_cast hn

theorem generatedPositiveFinite : GenericScalarTargets.GeneratedPositiveFinite := by
  intro f Γ ρ i t ht
  induction ht with
  | one i => exact ⟨zero_lt_one,fun _ => ⟨1,by simp [denoteWith]⟩⟩
  | omega i hi => exact ⟨Ordinal.omega0_pos,by intro h; omega⟩
  | var x j =>
    exact ⟨by change (0 : Ordinal) < ((ρ ⟨_,x,j⟩+1 : Nat) : Ordinal); exact_mod_cast Nat.zero_lt_succ _,
      fun _ => ⟨_,rfl⟩⟩
  | @add i a b ha hb ia ib =>
    refine ⟨sum_positive ia.1 (belowEpsilon f Γ ρ a) (belowEpsilon f Γ ρ b),?_⟩
    intro h
    obtain ⟨m,hm⟩ := ia.2 h
    obtain ⟨n,hn⟩ := ib.2 h
    exact ⟨m+n,ParametricSourceAddition.Proof.add_value f _ _ _ _ _ hm hn⟩
  | @emul i a b hi ha hb ia ib =>
    refine ⟨product_positive (Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))) ib.1
      (two_power_below (belowEpsilon f Γ ρ a)) (belowEpsilon f Γ ρ b),?_⟩
    intro h
    omega
  | @collapse a b ha hb ia ib =>
    exact ⟨collapse_pos f _ _ (belowEpsilon f Γ ρ a) (belowEpsilon f Γ ρ b) ib.1,
      fun _ => ⟨_,rfl⟩⟩

theorem actualSourceTotality : GenericScalarTargets.ActualSourceTotality := by
  intro p f Γ ρ t
  obtain ⟨v,hv,hg⟩ := actualAdmissibleAssignmentGenerated Γ .ground p t
  have hs := generatedPositiveFinite f Γ ρ 0 (v 0) (hg 0)
  obtain ⟨n,hn⟩ := hs.2 rfl
  have hp : 0 < n := by rw [hn] at hs; exact_mod_cast hs.1
  refine ⟨v,hv,n,hp,hn,?_⟩
  intro m
  constructor
  · intro hm
    exact CompositeEraser.scalarUniqueness p f Γ _ t m n hm ⟨v,hv,hn⟩
  · rintro rfl
    exact ⟨v,hv,hn⟩
#audit_namespace LogicLineages.ControlSensitivityCurrent.GenericScalar
end LogicLineages.ControlSensitivityCurrent.GenericScalar
