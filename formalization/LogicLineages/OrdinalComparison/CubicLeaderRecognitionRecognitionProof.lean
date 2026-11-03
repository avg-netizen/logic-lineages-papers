module
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionMassProof
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionInputProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionEntriesProof
public import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.OrdinalComparison.CubicLeaderRecognition.Proof
open CounterLeaderExpansion

private theorem modulus_comm (c e : Nat) : cubicModulus c e = cubicModulus e c := by
  simp only [cubicModulus, max_comm]

private theorem exact_modulus (c e : Nat) : cubicModulus c e =
    encodedPrincipalKernelMassModulus (rawNoteEncode (ONote.ofNat 3)) c e := by
  have hn : rawNormCode (rawNoteEncode (ONote.ofNat 3)) = 3 := by
    rw [rawNormCodeCorrect]
    rfl
  simp only [encodedPrincipalKernelMassModulus, encodedStrictMassSyntaxBound, hn,
    cubicModulus]
  omega

theorem actualCubicPairRecognition : Targets.ActualCubicPairRecognition := by
  refine ⟨exact_modulus, ?_⟩
  intro c e t u ht hu
  constructor
  · intro heq
    have htu : t = u := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (ne_of_lt (cubic_strict_inputs c e t u ht hu hlt)) heq
      · have hu' : cubicModulus e c ≤ u := by simpa only [modulus_comm e c] using hu
        have ht' : cubicModulus e c ≤ t := by simpa only [modulus_comm e c] using ht
        exact (ne_of_lt (cubic_strict_inputs e c u t hu' ht' hgt)) heq.symm
    subst u
    have hce : c = e := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (ne_of_lt (cubic_strict_mass c e t hlt ht)) heq.symm
      · have ht' : cubicModulus e c ≤ t := by simpa only [modulus_comm e c] using ht
        exact (ne_of_lt (cubic_strict_mass e c t hgt ht')) heq
    exact ⟨hce, rfl⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem actualLeaderRecognition : Targets.ActualLeaderRecognition := by
  intro n m c e t u ht hu
  have ht' : cubicModulus (c+3) (e+3) ≤ bottomInput n c t :=
    ((Nat.le_max_right _ _).trans ht).trans (CounterLeaderExpansion.Proof.bottomInput_ge n c t)
  have hu' : cubicModulus (c+3) (e+3) ≤ bottomInput m e u := by
    have h : cubicModulus (e+3) (c+3) ≤ bottomInput m e u :=
      ((Nat.le_max_right _ _).trans hu).trans (CounterLeaderExpansion.Proof.bottomInput_ge m e u)
    simpa only [modulus_comm (c+3) (e+3)] using h
  have hk := actualCubicPairRecognition.2 (c+3) (e+3)
    (bottomInput n c t) (bottomInput m e u) ht' hu'
  constructor
  · intro h
    change Phi (kernel 3 (c+3) (bottomInput n c t)) =
      Phi (kernel 3 (e+3) (bottomInput m e u)) at h
    obtain ⟨hc,hb⟩ := hk.mp (Phi_strictMono.injective h)
    exact ⟨by omega,hb⟩
  · rintro ⟨rfl,hb⟩
    simp only [leader, leaderPreimage, hb]

end LogicLineages.OrdinalComparison.CubicLeaderRecognition.Proof
