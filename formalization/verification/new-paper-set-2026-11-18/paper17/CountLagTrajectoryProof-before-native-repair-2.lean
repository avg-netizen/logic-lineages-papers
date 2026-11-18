module
public import LogicLineages.PermittedControl.CountLagTargets
public import LogicLineages.PermittedControl.PropagationProof
public import LogicLineages.PermittedControl.EntryTableProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem entry_trajectory_data (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lam mu : Ordinal.{0}) (t tau : Nat) (ha : lam < epsilonZero) (hl : Order.IsSuccLimit lam)
    (hmu : mu = 0 ∨ Order.IsSuccLimit mu) (hml : mu < lam)
    (ht : max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm mu)) ≤ t)
    (hhit : FirstEntry f (countInitial lam t) mu tau) :
    (∀ i : Nat, i ≤ tau →
      (descentWith f)^[i] (countInitial lam t) = mu + relativeState f lam mu t i ∧
      actualOrdinalNorm ((descentWith f)^[i] (countInitial lam t)) = f^[i] t ∧
      actualOrdinalNorm (relativeState f lam mu t i) ≤ f^[i] t ∧
      (relativeState f lam mu t i < Ordinal.omega0 ↔ i = tau)) ∧
    (∀ i : Nat, i < tau → relativeState f lam mu t (i+1) =
      relativeMaximum mu (actualLimitPart (relativeState f lam mu t i)) (f^[i+1] t)) := by
  obtain ⟨j,hj,hinit,hdata,hsteps⟩ := relativeEntryRecursion f B hf lam mu (lam-mu) t ha hl hmu hml
    (Ordinal.isSuccLimit_sub hl.isSuccPrelimit hml) (Ordinal.add_sub_cancel_of_le hml.le) ht
  have heq := firstEntry_unique f _ mu j tau hj hhit
  subst j
  exact ⟨hdata,hsteps⟩

 theorem relative_after_entry_finite (f : Nat → Nat) (lam mu : Ordinal.{0}) (t tau i : Nat)
    (ha : countInitial lam t < epsilonZero) (hhit : FirstEntry f (countInitial lam t) mu tau)
    (hi : tau ≤ i) : relativeState f lam mu t i < Ordinal.omega0 := by
  have hb : (descentWith f)^[i] (countInitial lam t) < mu+Ordinal.omega0 :=
    (trajectory_antitone f _ ha hi).trans_lt hhit.2.1
  unfold relativeState
  by_cases hm : mu ≤ (descentWith f)^[i] (countInitial lam t)
  · exact (Ordinal.sub_lt_of_le hm).mpr hb
  · rw [sub_eq_zero_of_le (le_of_lt (lt_of_not_ge hm))]
    exact Ordinal.omega0_pos

 theorem relative_positive_iff (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lam mu : Ordinal.{0}) (t tau : Nat) (ha : lam < epsilonZero) (hl : Order.IsSuccLimit lam)
    (hmu : mu = 0 ∨ Order.IsSuccLimit mu) (hml : mu < lam)
    (ht : max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm mu)) ≤ t)
    (hhit : FirstEntry f (countInitial lam t) mu tau) (i : Nat) :
    0 < actualLimitPart (relativeState f lam mu t i) ↔ i < tau := by
  have hin := count_initial_facts lam t ha hl (by omega)
  have hdata := entry_trajectory_data f B hf lam mu t tau ha hl hmu hml ht hhit
  constructor
  · intro hpos
    by_contra hn
    have hfin := relative_after_entry_finite f lam mu t tau i hin.1 hhit (by omega)
    obtain ⟨n, heq⟩ := Ordinal.lt_omega0.mp hfin
    rw [heq, limitPart_finite] at hpos
    exact (lt_irrefl 0) hpos
  · intro hi
    have hn : Ordinal.omega0 ≤ relativeState f lam mu t i := by
      apply le_of_not_gt
      intro hfin
      have heq := (hdata.1 i hi.le).2.2.2.mp hfin
      omega
    have hb : relativeState f lam mu t i < epsilonZero :=
      (Ordinal.sub_le_self _ _).trans_lt (trajectory_below f _ hin.1 i)
    exact (actualNonfiniteDecomposition _ hn hb).2.1.bot_lt

end LogicLineages.PermittedControl
