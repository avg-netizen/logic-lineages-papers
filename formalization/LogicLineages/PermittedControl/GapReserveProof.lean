module
public import LogicLineages.PermittedControl.GapInputFoundationProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem gap_reserves (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lam mu lam' mu' : Ordinal.{0}) (t tau k : Nat)
    (ha : lam < epsilonZero) (ha' : lam' < epsilonZero)
    (hl : Order.IsSuccLimit lam) (hl' : Order.IsSuccLimit lam')
    (hmu : mu = 0 ∨ Order.IsSuccLimit mu) (hml : mu < lam) (hml' : mu' < lam')
    (hgap : lam'-mu'+Ordinal.omega0*(k : Ordinal) ≤ lam-mu)
    (ht : gapInputTail lam mu lam' mu' k ≤ t)
    (hhit : FirstEntry f (countInitial lam t) mu tau) :
    k < tau ∧ lam'-mu' ≤ actualLimitPart (relativeState f lam mu t k) := by
  have htails := gap_tail_bounds lam mu lam' mu' k
  have ht' := htails.1.trans ht
  have hdata := entry_trajectory_data f B hf lam mu t tau ha hl hmu hml ht' hhit
  have hpos := relative_positive_iff f B hf lam mu t tau ha hl hmu hml ht' hhit
  have had := selected_threshold_admissible f B hf
  have hin := count_initial_facts lam t ha hl (by omega)
  have hd : Order.IsSuccLimit (lam'-mu') := Ordinal.isSuccLimit_sub hl'.isSuccPrelimit hml'
  have hdbelow : lam'-mu' < epsilonZero := (Ordinal.sub_le_self _ _).trans_lt ha'
  have hdnorm := gap_norm_le lam' mu' ha' hml'.le
  have hdom : ∀ j : Nat, j ≤ tau → mu+relativeState f lam mu t j < epsilonZero := by
    intro j hj
    rw [← (hdata.1 j hj).1]
    exact trajectory_below f _ hin.1 j
  have inv : ∀ j : Nat, j ≤ k → j < tau ∧
      lam'-mu'+Ordinal.omega0*((k-j : Nat) : Ordinal) ≤
        actualLimitPart (relativeState f lam mu t j) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hbase : lam'-mu'+Ordinal.omega0*(k : Ordinal) ≤
          actualLimitPart (relativeState f lam mu t 0) := by
        rw [gap_initial_limit f lam mu t hl hml]
        exact hgap
      have hpositive := hd.bot_lt.trans_le (le_self_add.trans hbase)
      exact ⟨(hpos 0).mp hpositive, by simpa using hbase⟩
    | succ j ih =>
      intro hjk
      have hjlt : j < k := by omega
      obtain ⟨hjrun,hreserve⟩ := ih (by omega)
      let r := k-(j+1)
      have hr : r+1 = k-j := by dsimp [r]; omega
      have hstrict : lam'-mu'+Ordinal.omega0*(r : Ordinal) <
          lam'-mu'+Ordinal.omega0*((k-j : Nat) : Ordinal) := by
        rw [← hr, Nat.cast_add, Nat.cast_one, mul_add, mul_one, ← add_assoc]
        simpa using (add_lt_add_iff_left (lam'-mu'+Ordinal.omega0*(r : Ordinal))).mpr Ordinal.omega0_pos
      have hcandidate := hstrict.trans_le hreserve
      have hrnorm := reserve_norm_le (lam'-mu') hdbelow r
      have hcost := (relativeNorm mu (lam'-mu'+Ordinal.omega0*(r : Ordinal))
        (hml.trans ha) hrnorm.1).2.2
      have hiter : t ≤ f^[j+1] t := iterate_self_le (control_self_le f had.2) _ _
      have hrle : r ≤ k := by dsimp [r]; omega
      have hpaid : actualOrdinalNorm (lam'-mu'+Ordinal.omega0*(r : Ordinal)) +
          relativeCost mu (lam'-mu'+Ordinal.omega0*(r : Ordinal)) ≤ f^[j+1] t := by
        have htail := htails.2.2.2
        have hn := hrnorm.2
        omega
      have hbudget : actualOrdinalNorm mu ≤ f^[j+1] t := by
        have htail := htails.1
        omega
      have hlimbelow : mu+actualLimitPart (relativeState f lam mu t j) < epsilonZero :=
        (add_le_add_right (Ordinal.mul_div_le _ Ordinal.omega0) mu).trans_lt (hdom j hjrun.le)
      have hmax := (relativeMaximumSpec mu (actualLimitPart (relativeState f lam mu t j))
        (f^[j+1] t) hlimbelow ((hpos j).mpr hjrun) hbudget).2
      have hle := hmax.2 ⟨hcandidate,hpaid⟩
      have hproject := actualLimitPartMonotone hle
      have hfixed : actualLimitPart (lam'-mu'+Ordinal.omega0*(r : Ordinal)) =
          lam'-mu'+Ordinal.omega0*(r : Ordinal) := by
        simpa using limitPart_tail _ (reserve_limit _ hd r) 0
      rw [hfixed, ← hdata.2 j hjrun] at hproject
      have hpositive := hd.bot_lt.trans_le (le_self_add.trans hproject)
      exact ⟨(hpos (j+1)).mp hpositive, hproject⟩
  have h := inv k le_rfl
  simpa using h

end LogicLineages.PermittedControl
