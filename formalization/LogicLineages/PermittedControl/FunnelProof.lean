module
public import LogicLineages.PermittedControl.CountTargets
public import LogicLineages.PermittedControl.FiniteCoefficientProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

theorem selected_threshold_admissible (f : Nat → Nat) (B : Nat) (h : SelectedWithThreshold f B) :
    StrictMono f ∧ ∀ n, G n ≤ f n := by
  apply selected_admissibility
  rcases h with ⟨rfl, _⟩ | ⟨b, rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨b, rfl⟩

theorem selected_even (f : Nat → Nat) (B : Nat) (h : SelectedWithThreshold f B) (n : Nat) : 2 ∣ f n := by
  rcases h with ⟨rfl, _⟩ | ⟨b, rfl, _⟩
  · exact factorialControl_even n
  · exact nearControl_even b n

theorem selected_orbit (f : Nat → Nat) (B : Nat) (h : SelectedWithThreshold f B)
    (m t i : Nat) (hm : 0 < m) (ht : max m B ≤ t) :
    Int.ModEq (m : Int) (potential (f^[i] t) : Int) ((potential t : Int) - (i : Int)) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨b, rfl, rfl⟩
  · exact factorialControlOrbit m t i hm ht
  · exact nearControlOrbit b m t i hm ht

theorem limitPart_tail (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem square_facts :
    Ordinal.omega0 ^ (2 : Ordinal.{0}) < epsilonZero ∧
    actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal.{0})) = 3 ∧
    Order.IsSuccLimit (Ordinal.omega0 ^ (2 : Ordinal.{0})) := by
  have h := actualFiniteMonomialFacts 2 1
  have he : Ordinal.omega0 ^ (2 : Ordinal.{0}) = Ordinal.omega0 * Ordinal.omega0 := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, Ordinal.opow_add, Ordinal.opow_one]
  refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
  rw [he]
  exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 Ordinal.omega0_pos

theorem funnel_state (f : Nat → Nat) (hmono : StrictMono f) (hf : ∀ n, G n ≤ f n)
    (heven : ∀ n, 2 ∣ f n) (a : Ordinal) (ha : a < epsilonZero)
    (hhigh : Ordinal.omega0 ^ (2 : Ordinal.{0}) ≤ actualLimitPart a) :
    ∃ i : Nat,
      actualLimitPart ((descentWith f)^[i] a) = Ordinal.omega0 ^ (2 : Ordinal.{0}) ∧
      actualOrdinalNorm ((descentWith f)^[i] a) = f^[i] (actualOrdinalNorm a) ∧
      (terminalWith f a).2 = i + 1 + potential (f (f^[i] (actualOrdinalNorm a))) := by
  revert ha hhigh
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha hhigh
    have hw : Ordinal.omega0 ≤ a :=
      (Ordinal.omega0_le_of_isSuccLimit square_facts.2.2).trans
        (hhigh.trans (Ordinal.mul_div_le a Ordinal.omega0))
    have hd := descent_strict f a hw ha
    have hn := descent_norm f a hw ha
    have hc := (terminal_nonfinite f a ha hw).2
    have hb : 2 ≤ f (actualOrdinalNorm a) := by
      have h := G_large (actualOrdinalNorm a)
      have h' := hf (actualOrdinalNorm a)
      omega
    by_cases heq : actualLimitPart a = Ordinal.omega0 ^ (2 : Ordinal.{0})
    · have hs : descentWith f a = Ordinal.omega0 * ((f (actualOrdinalNorm a) / 2 : Nat) : Ordinal) + (0 : Ordinal) := by
        unfold descentWith
        rw [heq, actualOmegaSquaredMaximum _ hb, Nat.mod_eq_zero_of_dvd (heven _)]
        rfl
      have hl := (finiteCoefficientTerminal f hmono hf (f (actualOrdinalNorm a) / 2) 0).1
      simp only [Nat.cast_zero] at hl
      rw [← hs] at hl
      refine ⟨0, heq, rfl, ?_⟩
      simp only [Function.iterate_zero_apply, potential]
      omega
    · have hlt : Ordinal.omega0 ^ (2 : Ordinal.{0}) < actualLimitPart a := lt_of_le_of_ne hhigh (Ne.symm heq)
      have hdecomp := actualNonfiniteDecomposition a hw ha
      have hm := actualMaximumPredecessor_correct (actualLimitPart a) hdecomp.2.1.bot_lt hdecomp.1
        (f (actualOrdinalNorm a))
      have hbudget : actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal.{0})) ≤ f (actualOrdinalNorm a) := by
        rw [square_facts.2.1]
        have h := G_large (actualOrdinalNorm a)
        have h' := hf (actualOrdinalNorm a)
        omega
      have hstep : Ordinal.omega0 ^ (2 : Ordinal.{0}) ≤ descentWith f a := hm.2 ⟨hlt, hbudget⟩
      have hlp : Ordinal.omega0 ^ (2 : Ordinal.{0}) ≤ actualLimitPart (descentWith f a) := by
        have h := actualLimitPartMonotone hstep
        have he : actualLimitPart (Ordinal.omega0 ^ (2 : Ordinal.{0})) = Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
          simpa using limitPart_tail _ square_facts.2.2 0
        rwa [he] at h
      obtain ⟨i, hi, hiNorm, hiCount⟩ := ih (descentWith f a) hd (hd.trans ha) hlp
      refine ⟨i + 1, ?_, ?_, ?_⟩
      · simpa only [Function.iterate_succ_apply] using hi
      · simpa only [Function.iterate_succ_apply, hn] using hiNorm
      · rw [Function.iterate_succ_apply]
        rw [hn] at hiCount
        omega

theorem highHeadFunnel : Targets.HighHeadFunnel := by
  intro f B hf lam t hlam hlim hhigh ht
  have had := selected_threshold_admissible f B hf
  have hi := actualFiniteTailClosureNorm lam hlam (t - actualOrdinalNorm lam)
  have hin : actualOrdinalNorm (countInitial lam t) = t := by
    change actualOrdinalNorm (lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)) = t
    rw [hi.2, Nat.add_sub_of_le ht]
  have hlp : actualLimitPart (countInitial lam t) = lam := limitPart_tail lam hlim _
  have h := funnel_state f had.1 had.2 (selected_even f B hf) (countInitial lam t) hi.1 (by rwa [hlp])
  simpa only [hin, completeCount] using h

end LogicLineages.PermittedControl
