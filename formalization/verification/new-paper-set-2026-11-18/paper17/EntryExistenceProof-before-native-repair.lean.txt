module
public import LogicLineages.PermittedControl.EntryBasicsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem entry_exists_state (f : Nat → Nat) (hf : ∀ n, G n ≤ f n)
    (nu : Ordinal.{0}) (hnu : nu = 0 ∨ Order.IsSuccLimit nu)
    (a : Ordinal.{0}) (ha : a < epsilonZero) (hlo : nu ≤ a)
    (hbudget : actualOrdinalNorm nu ≤ actualOrdinalNorm a) :
    ∃ i : Nat, FirstEntry f a nu i ∧ entryNormAt f a i = f^[i] (actualOrdinalNorm a) := by
  revert ha hlo hbudget
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha hlo hbudget
    by_cases hhit : a < nu + Ordinal.omega0
    · exact ⟨0, ⟨hlo, hhit, by intro j hj; omega⟩, rfl⟩
    · have hw : Ordinal.omega0 ≤ a :=
        (le_add_self : Ordinal.omega0 ≤ nu + Ordinal.omega0).trans (le_of_not_gt hhit)
      have hdecomp := actualNonfiniteDecomposition a hw ha
      have hlpnu : actualLimitPart nu = nu := by
        rcases hnu with rfl | hnu
        · exact limitPart_finite 0
        · simpa using limitPart_tail nu hnu 0
      have hle : nu ≤ actualLimitPart a := by
        have h := actualLimitPartMonotone hlo
        rwa [hlpnu] at h
      have hneq : actualLimitPart a ≠ nu := by
        intro heq
        exact hhit ((interval_iff_limitPart a nu hnu).mpr heq).2
      have hlt : nu < actualLimitPart a := lt_of_le_of_ne hle (Ne.symm hneq)
      have hnorm : actualOrdinalNorm nu ≤ f (actualOrdinalNorm a) :=
        hbudget.trans (control_self_le f hf _)
      have hmax := actualMaximumPredecessor_correct (actualLimitPart a) hdecomp.2.1.bot_lt hdecomp.1
        (f (actualOrdinalNorm a))
      have hnext : nu ≤ descentWith f a := hmax.2 ⟨hlt, hnorm⟩
      have hd := descent_strict f a hw ha
      have hn := descent_norm f a hw ha
      obtain ⟨i, hi, horbit⟩ := ih (descentWith f a) hd (hd.trans ha) hnext (by rwa [hn])
      refine ⟨i + 1, ⟨?_, ?_, ?_⟩, ?_⟩
      · simpa only [Function.iterate_succ_apply] using hi.1
      · simpa only [Function.iterate_succ_apply] using hi.2.1
      · intro j hj henter
        cases j with
        | zero => exact hhit henter.2
        | succ j =>
          apply hi.2.2 j (by omega)
          simpa only [Function.iterate_succ_apply] using henter
      · simpa only [entryNormAt, Function.iterate_succ_apply, hn] using horbit

theorem entryExistenceOrbit : Targets.EntryExistenceOrbit := by
  intro f B hf lam nu t ha hl hnu hlt ht
  have had := selected_threshold_admissible f B hf
  have hstate := actualFiniteTailClosureNorm lam ha (t - actualOrdinalNorm lam)
  have hn : actualOrdinalNorm (countInitial lam t) = t := by
    change actualOrdinalNorm (lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)) = t
    rw [hstate.2, Nat.add_sub_of_le (by omega)]
  have h := entry_exists_state f had.2 nu hnu (countInitial lam t) hstate.1
    (hlt.le.trans le_self_add) (by rw [hn]; omega)
  simpa only [hn] using h

end LogicLineages.PermittedControl
