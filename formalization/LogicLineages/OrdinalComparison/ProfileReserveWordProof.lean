module
public import LogicLineages.OrdinalComparison.ProfileReserveWordTargets
public import LogicLineages.OrdinalComparison.ProfileReserveBudgetProof
public import LogicLineages.OrdinalComparison.ReserveEndpointProof
public import LogicLineages.OrdinalComparison.ReserveStageProof
public import LogicLineages.OrdinalComparison.ProfileCompilerProof
public import LogicLineages.OrdinalComparison.HeadEndpointProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualValidProfileWordStrictMono (word : List NONote)
    (hv : ∀ rho ∈ word, Order.IsSuccLimit rho.1.repr) :
    StrictMono (actualProfileWordValue word) := by
  induction word with
  | nil => intro x y h; exact h
  | cons rho word ih =>
    intro x y h
    exact ih (fun sigma hs => hv sigma (List.mem_cons_of_mem rho hs))
      ((actualFixedLimitProfileHeads rho (hv rho (by simp))).1 h)

private theorem reserve_terminal_nat (n : Nat) : actualTerminalValue (n : Ordinal) = n := by
  have hz := normalRepresentationSound ⟨ONote.zero, ONote.NF.zero⟩
  have he := (actualFiniteTailClosureNorm 0 (by simpa [ONote.repr] using hz) n).1
  simp only [zero_add] at he
  have hc := (actualControlledCountRecursion Phi (n : Ordinal) he).1 (Ordinal.natCast_lt_omega0 n)
  have hv := (actualTerminalValueIdentities (n : Ordinal) he).2
  rw [← actualControlledCountPhiAgreement (n : Ordinal) he, hc, Function.iterate_zero_apply] at hv
  have hn : actualOrdinalNorm (n : Ordinal) = n := by
    simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.mul_zero, Nat.zero_add] using actualFiniteHeadNorm 0 n
  exact hv.trans hn

private theorem reserve_head_formula (rho : NONote) (n : Nat) :
    actualProfileHead rho n =
      (Phi^[actualControlledCount Phi (rho.1.repr + (n : Ordinal))]) (actualOrdinalNorm rho.1.repr + n) +
        actualControlledCount Phi (rho.1.repr + (n : Ordinal)) := by
  have hi := actualFiniteTailClosureNorm rho.1.repr (normalRepresentationSound rho) n
  have hv := actualTerminalValueIdentities (rho.1.repr + (n : Ordinal)) hi.1
  unfold actualProfileHead
  rw [hv.1, hv.2, ← actualControlledCountPhiAgreement _ hi.1, hi.2]

theorem actualProfileReserveWordConsumer : Targets.ActualProfileReserveWordConsumer := by
  intro beta hb he word
  induction word with
  | nil =>
    intro _ n
    simp [profileReserveBlocks, actualProfileWordValue, reserve_terminal_nat]
  | cons rho word ih =>
    intro hv n
    dsimp only
    let pi := Ordinal.omega0 ^ beta
    let R := profileReserveBlocks word
    let m := Vendor.R1.treeWeight rho.1 + 1
    let x := actualOrdinalNorm rho.1.repr + n
    let A := pi * ((R + m : Nat) : Ordinal) + (n : Ordinal)
    let c := R * actualOrdinalNorm pi
    let remnant := pi * (m : Ordinal) + (n : Ordinal)
    let C := actualControlledCount (compensatedPrefixControl c) remnant
    have hrho := hv rho (by simp)
    have htail : ∀ sigma ∈ word, Order.IsSuccLimit sigma.1.repr ∧ actualProfileLeadingMonomial sigma ≤ pi :=
      fun sigma hs => hv sigma (List.mem_cons_of_mem rho hs)
    have hm : m = actualOrdinalNorm rho.1.repr + 1 := by
      rw [actualOrdinalNorm_notationCorrespondence rho]
    have hmpos : 1 ≤ m := by omega
    have hbound : rho.1.repr < pi * (m : Ordinal) := by
      rw [hm]
      exact actualProfileReserveEligibility beta hb he rho hrho.1 hrho.2
    have hpl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
    have hw : 0 < actualOrdinalNorm pi := by
      have hn := actualNonfiniteNormLowerBound pi he (Ordinal.omega0_le_of_isSuccLimit hpl)
      omega
    have hq := reserveStagePrincipalMultipleFacts beta he (R + m)
    have hA := actualFiniteTailClosureNorm (pi * ((R + m : Nat) : Ordinal)) hq.1 n
    have hformula : actualOrdinalNorm A = (R + m) * actualOrdinalNorm pi + n := by
      change actualOrdinalNorm (pi * ((R + m : Nat) : Ordinal) + (n : Ordinal)) = _
      rw [hA.2, hq.2]
    have hx : actualOrdinalNorm rho.1.repr ≤ x := Nat.le_add_right _ _
    have hxA : x ≤ actualOrdinalNorm A := by
      rw [hformula]
      have hmul := Nat.le_mul_of_pos_right (R + m) hw
      dsimp only [x]
      omega
    have hs := fullActualOneStageReserve beta hb he R m n x hmpos rho.1.repr hrho.1 hbound hx hxA
    dsimp only at hs
    obtain ⟨n', hstate, hlarge⟩ := hs.2.2.2
    have hhead : actualProfileHead rho n < n' := by
      rw [reserve_head_formula]
      simpa only [x, Nat.add_sub_cancel_left] using hlarge
    have hcount : C ≤ actualControlledCount Phi A := by
      by_contra hnot
      have hlt : actualControlledCount Phi A < C := by omega
      have hnon := hs.2.2.1 (actualControlledCount Phi A) hlt
      have hfin := (actualControlledTraceFirstFinite Phi A hA.1).1
      have hlow : Ordinal.omega0 ≤ pi * (R : Ordinal) + Ordinal.omega0 := le_add_self
      exact not_lt_of_ge (hlow.trans hnon) hfin
    have hend := actualPhiEndpointAlongTrace A hA.1 C hcount
    rw [hstate] at hend
    have hrest := ih htail n'
    have hmono := actualValidProfileWordStrictMono word (fun sigma hs => (htail sigma hs).1)
    have hstrict : actualProfileWordValue (rho :: word) n < actualTerminalValue A :=
      ((hmono hhead).trans_le hrest.1).trans_eq hend
    have hR : profileReserveBlocks (rho :: word) = R + m := by
      simp [profileReserveBlocks, R, m, Nat.add_comm]
    rw [hR]
    exact ⟨hstrict.le, fun _ => hstrict⟩

end LogicLineages.OrdinalComparison
