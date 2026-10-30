module

public import LogicLineages.OrdinalComparison.SourceSuccessorCodingTargets
public import LogicLineages.OrdinalComparison.SourceApplicativeProof
public import LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibrationProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.ElementaryControl

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSuccessorCodingProof
open Targets
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics WWOmegaFiniteCalibration

theorem successorProbeDenotation : SuccessorProbeDenotation := by
  intro Γ x ρ n v hρ hv
  rw [SourceApplicativeProof.successorProbeAssignment Γ x] at hv
  have he := Option.some.inj hv
  subst v
  change (actualCollapse (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1)
    (ordinalNaturalSum 1 (ρ ⟨.ground, x, 0⟩))) : Ordinal) = _
  rw [hρ]
  have hs : ordinalNaturalSum 1 ((n + 1 : Nat) : Ordinal) = ((n + 2 : Nat) : Ordinal) := by
    simpa only [Nat.cast_one, Nat.add_comm 1 (n + 1), Nat.add_assoc] using
      WWOrdinalTermSemanticsProof.naturalSum_finite 1 (n + 1)
  rw [hs]
  simp only [successorRaw, block, Nat.cast_one]

theorem successorObservationCalibration : SuccessorObservationCalibration := by
  intro n
  have hr : successorRaw n = Phi (n + 4) + 1 := by
    unfold successorRaw block
    rw [WWOmegaFiniteCalibrationProof.productCalibration 1,
      WWOmegaFiniteCalibrationProof.sumCalibration 1 (n + 2), actualFiniteHeadCollapse]
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  exact ⟨hr, by simp [successorObservation, hr]⟩

theorem successorObservationGrowth : SuccessorObservationGrowth := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [(successorObservationCalibration n).2]
    have h := self_lt_Phi (n + 4)
    omega
  · intro a b hab
    rw [(successorObservationCalibration a).2, (successorObservationCalibration b).2]
    exact Phi_strictMono (by omega)
  · intro n
    rw [(successorObservationCalibration n).2, (successorObservationCalibration (n + 1)).2]
    have h := Phi_linear_gap (n + 4)
    have he : n + 1 + 4 = n + 4 + 1 := by omega
    rw [he]
    omega

private theorem sorted_pair_unique (a b c d : Nat) (hab : a ≤ b) (hcd : c ≤ d)
    (h : successorObservation a + successorObservation b = successorObservation c + successorObservation d) :
    a = c ∧ b = d := by
  have hmono := successorObservationGrowth.2.1.monotone
  have hgap := successorObservationGrowth.2.2
  have hbd : b ≤ d := by
    by_contra hn
    have hdb : d + 1 ≤ b := by omega
    have hsmall := hmono hcd
    have hlarge := (hgap d).trans_le (hmono hdb)
    omega
  have hdb : d ≤ b := by
    by_contra hn
    have hbd' : b + 1 ≤ d := by omega
    have hsmall := hmono hab
    have hlarge := (hgap b).trans_le (hmono hbd')
    omega
  have he : b = d := by omega
  subst d
  refine ⟨successorObservationGrowth.2.1.injective (by omega), rfl⟩

theorem successorPairCoding : SuccessorPairCoding := by
  intro a b c d
  constructor
  · intro h
    rcases le_total a b with hab | hba
    · rcases le_total c d with hcd | hdc
      · exact Or.inl (sorted_pair_unique a b c d hab hcd h)
      · exact Or.inr (sorted_pair_unique a b d c hab hdc (by omega))
    · rcases le_total c d with hcd | hdc
      · have hh := sorted_pair_unique b a c d hba hcd (by omega)
        exact Or.inr ⟨hh.2, hh.1⟩
      · have hh := sorted_pair_unique b a d c hba hdc (by omega)
        exact Or.inl ⟨hh.2, hh.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

theorem successorSortedWitness : SuccessorSortedWitness := by
  intro a b low high difference
  rw [successorPairCoding]
  constructor
  · rintro ⟨hp, hd⟩
    rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst low
      subst high
      have hab : a ≤ b := by omega
      simp only [min_eq_left hab, max_eq_right hab, true_and]
      omega
    · subst high
      subst low
      have hba : b ≤ a := by omega
      simp only [min_eq_right hba, max_eq_left hba, true_and]
      omega
  · rintro ⟨rfl, rfl, rfl⟩
    constructor
    · rcases le_total a b with h | h
      · exact Or.inl ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
      · exact Or.inr ⟨(max_eq_left h).symm, (min_eq_right h).symm⟩
    · have h : min a b ≤ max a b := min_le_max
      omega

end LogicLineages.OrdinalComparison.Source.SourceSuccessorCodingProof
