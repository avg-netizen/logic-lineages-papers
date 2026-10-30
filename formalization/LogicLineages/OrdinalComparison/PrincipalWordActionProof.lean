module
public import LogicLineages.OrdinalComparison.PrincipalWordActionTargets
public import LogicLineages.OrdinalComparison.PrincipalBlockDomainProof
public import LogicLineages.OrdinalComparison.PrincipalKernelWordProof
public import LogicLineages.OrdinalComparison.SuccessorKernelCutProof
public import LogicLineages.OrdinalComparison.ControlSegmentProof
public import LogicLineages.OrdinalComparison.ControlScheduleProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem word_run_append (v w : List (ONote × Nat)) (t : Nat) :
    actualPrincipalWordRun (v ++ w) t =
      ((actualPrincipalWordRun w (actualPrincipalWordRun v t).1).1,
       (actualPrincipalWordRun v t).2 + (actualPrincipalWordRun w (actualPrincipalWordRun v t).1).2) := by
  induction v generalizing t with
  | nil => simp [actualPrincipalWordRun]
  | cons p v ih =>
    rcases p with ⟨e, a⟩
    simp [actualPrincipalWordRun, ih, Nat.add_assoc]

private theorem word_genuine_append (v w : List (ONote × Nat)) (t : Nat) :
    actualPrincipalWordGenuine (v ++ w) t ↔
      actualPrincipalWordGenuine v t ∧ actualPrincipalWordGenuine w (actualPrincipalWordRun v t).1 := by
  induction v generalizing t with
  | nil => simp [actualPrincipalWordGenuine, actualPrincipalWordRun]
  | cons p v ih =>
    rcases p with ⟨e, a⟩
    simp [actualPrincipalWordGenuine, actualPrincipalWordRun, ih, and_assoc]

private theorem word_control_iterate (c n i : Nat) :
    c + ((compensatedPrefixControl c)^[i]) n = (Phi^[i]) (c + n) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hb := self_lt_Phi (c + ((compensatedPrefixControl c)^[i]) n)
    change c + (Phi (c + ((compensatedPrefixControl c)^[i]) n) - c) = _
    rw [Nat.add_sub_of_le (by omega), ih]

private theorem word_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.mul_zero, Nat.zero_add] using actualFiniteHeadNorm 0 n

private theorem word_single_facts (e : ONote) (he : ONote.NF e) :
    Ordinal.omega0 ^ e.repr < epsilonZero ∧
      actualOrdinalNorm (Ordinal.omega0 ^ e.repr) = 1 + Vendor.R1.treeWeight e := by
  letI := he
  let o : NONote := ⟨ONote.oadd e 1 0, inferInstance⟩
  exact ⟨by simpa [o, ONote.repr] using normalRepresentationSound o,
    by simpa [o, ONote.repr, Vendor.R1.treeWeight] using actualOrdinalNorm_notationCorrespondence o⟩

private theorem word_calibration (es : List ONote) (hg : GenuinePrincipalBlocks es) (c n : Nat) :
    let t := c + principalBlocksWeight es + n
    let C := actualControlledCount (compensatedPrefixControl c) (principalBlockSum es + (n : Ordinal))
    actualPrincipalWordRun (principalKernelWord es c) t = ((Phi^[C]) t, C) ∧
    actualPrincipalWordGenuine (principalKernelWord es c) t := by
  induction es generalizing c with
  | nil =>
    have hs := (actualPrincipalBlockSumDomain [] hg).1
    have hn := (actualFiniteTailClosureNorm 0 (by simpa [principalBlockSum] using hs) n).1
    simp only [zero_add] at hn
    have hc := (actualControlledCountRecursion (compensatedPrefixControl c) (n : Ordinal) hn).1
      (Ordinal.natCast_lt_omega0 n)
    simpa [principalBlockSum, principalBlocksWeight, principalKernelWord,
      actualPrincipalWordRun, actualPrincipalWordGenuine, hc]
  | cons e es ih =>
    let theta := Ordinal.omega0 ^ e.repr
    let w := 1 + Vendor.R1.treeWeight e
    let R := principalBlockSum es + (n : Ordinal)
    let T := c + w + principalBlocksWeight es + n
    let C := actualControlledCount (compensatedPrefixControl (c + w)) R
    let K := (Phi^[C]) T
    have he := hg.1 e (by simp)
    have hp := List.pairwise_cons.mp hg.2
    have htail : GenuinePrincipalBlocks es :=
      ⟨fun f hf => hg.1 f (List.mem_cons_of_mem e hf), hp.2⟩
    have hdom := actualPrincipalBlockSumDomain es htail
    have hR := actualFiniteTailClosureNorm (principalBlockSum es) hdom.1 n
    have htheta := word_single_facts e he.1
    have hnormR : actualOrdinalNorm R = principalBlocksWeight es + n := by
      rw [hR.2, hdom.2.1]
    have hbR : R < Ordinal.omega0 ^ (e.repr + 1) :=
      actualPrincipalBlockUpperBound es e.repr he.2 hp.1 n
    have hmin : actualMinExponentAtLeast theta e.repr :=
      (actualMinExponentDivisibility theta htheta.1 e.repr).mpr (dvd_refl _)
    have hbudget : ∀ k : Nat, actualOrdinalNorm theta ≤
        compensatedPrefixControl c (actualOrdinalNorm theta + k) := by
      intro k
      have hh := (compensatedPrefixControlBounds c).2 (actualOrdinalNorm theta + k)
      omega
    have hsplit := actualRetainedPrefixCountDecomposition (compensatedPrefixControl c)
      theta R htheta.1 hR.1 e.repr he.2 hmin hbR hbudget
    dsimp only at hsplit
    rw [htheta.2, actualCompensatedControlComposition] at hsplit
    obtain ⟨m, hm, hcount⟩ := hsplit.2.2
    have htrace := actualControlledNormIteration (compensatedPrefixControl (c + w)) R hR.1 C le_rfl
    have htotal := word_control_iterate (c + w) (actualOrdinalNorm R) C
    rw [← htrace, hm, word_nat_norm, hnormR] at htotal
    have hK : c + w + m = K := by
      simpa only [K, T, Nat.add_assoc] using htotal
    have hinit : actualSuffixKernelInitial theta c K = theta + (m : Ordinal) := by
      unfold actualSuffixKernelInitial
      rw [htheta.2]
      have hm' : K - c - w = m := by omega
      rw [hm']
    have hfinal : actualControlledCount (compensatedPrefixControl c) (theta + R) =
        C + actualSuffixKernelCount theta c K := by
      change actualControlledCount (compensatedPrefixControl c) (theta + R) =
        C + actualControlledCount (compensatedPrefixControl c) (actualSuffixKernelInitial theta c K)
      rw [hinit]
      exact hcount
    have hit := ih htail (c + w)
    have hitrun : actualPrincipalWordRun (principalKernelWord es (c + w)) T = (K, C) := hit.1
    have hitgen : actualPrincipalWordGenuine (principalKernelWord es (c + w)) T := hit.2
    have hT : c + principalBlocksWeight (e :: es) + n = T := by
      simp [principalBlocksWeight, T, w, Nat.add_assoc]
    have hsum : principalBlockSum (e :: es) + (n : Ordinal) = theta + R := by
      simp [principalBlockSum, theta, R, add_assoc]
    dsimp only
    rw [hT, hsum]
    constructor
    · change actualPrincipalWordRun (principalKernelWord es (c + w) ++ [(e, c)]) T = _
      rw [word_run_append, hitrun]
      simp only [actualPrincipalWordRun, Nat.add_zero, hfinal]
      apply Prod.ext
      · change (Phi^[actualSuffixKernelCount theta c K]) K =
          (Phi^[C + actualSuffixKernelCount theta c K]) T
        rw [Nat.add_comm C, Function.iterate_add_apply]
      · rfl
    · change actualPrincipalWordGenuine (principalKernelWord es (c + w) ++ [(e, c)]) T
      rw [word_genuine_append, hitrun]
      refine ⟨hitgen, ?_⟩
      change c + actualOrdinalNorm theta ≤ K ∧ True
      rw [htheta.2]
      exact ⟨by omega, trivial⟩

theorem actualPrincipalWordRunCorrect : Targets.ActualPrincipalWordRunCorrect := by
  intro es hg c n
  exact (word_calibration es hg c n).1

theorem actualPrincipalWordInputsGenuine : Targets.ActualPrincipalWordInputsGenuine := by
  intro es hg c n
  exact (word_calibration es hg c n).2

end LogicLineages.OrdinalComparison
