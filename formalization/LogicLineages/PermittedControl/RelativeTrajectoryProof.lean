module
public import LogicLineages.PermittedControl.RelativeMaximumProof
public import LogicLineages.PermittedControl.CountProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem descent_le (f : Nat → Nat) (a : Ordinal.{0}) (ha : a < epsilonZero) :
    descentWith f a ≤ a := by
  by_cases hn : Ordinal.omega0 ≤ a
  · exact (descent_strict f a hn ha).le
  · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (lt_of_not_ge hn)
    rw [descent_finite]
    exact zero_le

 theorem trajectory_below (f : Nat → Nat) (a : Ordinal.{0}) (ha : a < epsilonZero) (i : Nat) :
    (descentWith f)^[i] a < epsilonZero := by
  induction i with
  | zero => exact ha
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (descent_le f _ ih).trans_lt ih

 theorem trajectory_antitone (f : Nat → Nat) (a : Ordinal.{0}) (ha : a < epsilonZero) :
    Antitone (fun i : Nat => (descentWith f)^[i] a) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [Function.iterate_succ_apply']
  exact descent_le f _ (trajectory_below f a ha i)

 theorem trajectory_norm (f : Nat → Nat) (a : Ordinal.{0}) (ha : a < epsilonZero)
    (i : Nat) (hi : i ≤ (terminalWith f a).2) :
    actualOrdinalNorm ((descentWith f)^[i] a) = f^[i] (actualOrdinalNorm a) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hn := (terminal_firstFinite f a ha).2 i (by omega)
    rw [Function.iterate_succ_apply', descent_norm f _ hn (trajectory_below f a ha i),
      ih (by omega), Function.iterate_succ_apply']

 theorem relativeEntryRecursion : Targets.RelativeEntryRecursion := by
  intro f B hf lam mu delta t ha hl hmu hml hd hgap ht
  obtain ⟨tau, hhit, horbit⟩ := entryExistenceOrbit f B hf lam mu t ha hl hmu hml ht
  have had := selected_threshold_admissible f B hf
  have hlt : actualOrdinalNorm lam ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hmt : actualOrdinalNorm mu ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hin := count_initial_facts lam t ha hl hlt
  have hmuBelow : mu < epsilonZero := hml.trans ha
  have htau := firstEntry_le_terminal f (countInitial lam t) mu hin.1 hmu tau hhit
  have hstate : ∀ i : Nat, i ≤ tau →
      (descentWith f)^[i] (countInitial lam t) = mu + relativeState f lam mu t i := by
    intro i hi
    exact (Ordinal.add_sub_cancel_of_le
      (hhit.1.trans (trajectory_antitone f _ hin.1 hi))).symm
  have hnorm : ∀ i : Nat, i ≤ tau →
      actualOrdinalNorm ((descentWith f)^[i] (countInitial lam t)) = f^[i] t := by
    intro i hi
    rw [trajectory_norm f _ hin.1 i (hi.trans htau), hin.2.1]
  have hrelativeBelow : ∀ i : Nat, i ≤ tau → relativeState f lam mu t i < epsilonZero := by
    intro i hi
    have hb := trajectory_below f _ hin.1 i
    rw [hstate i hi] at hb
    exact (le_add_self : relativeState f lam mu t i ≤ mu+relativeState f lam mu t i).trans_lt hb
  have hfinite : ∀ i : Nat, i ≤ tau →
      (relativeState f lam mu t i < Ordinal.omega0 ↔ i = tau) := by
    intro i hi
    constructor
    · intro hfin
      by_contra hne
      have hbefore : i < tau := lt_of_le_of_ne hi hne
      apply hhit.2.2 i hbefore
      rw [hstate i hi]
      exact ⟨le_self_add, (add_lt_add_iff_left mu).mpr hfin⟩
    · intro heq
      subst i
      apply (add_lt_add_iff_left mu).mp
      rw [← hstate tau le_rfl]
      exact hhit.2.1
  refine ⟨tau, hhit, ?_, ?_, ?_⟩
  · simp only [relativeState, Function.iterate_zero_apply, countInitial]
    rw [← hgap, add_assoc, Ordinal.add_sub_cancel]
  · intro i hi
    refine ⟨hstate i hi, hnorm i hi, ?_, hfinite i hi⟩
    have hcost := (relativeNorm mu (relativeState f lam mu t i) hmuBelow (hrelativeBelow i hi)).1
    have hn := hnorm i hi
    rw [hstate i hi, hcost] at hn
    omega
  · intro i hi
    have his : i+1 ≤ tau := by omega
    have hy : Ordinal.omega0 ≤ relativeState f lam mu t i := by
      apply le_of_not_gt
      intro hfin
      have heq := (hfinite i hi.le).mp hfin
      omega
    have hbudget : actualOrdinalNorm mu ≤ f^[i+1] t := by
      have hg : t ≤ f^[i+1] t := by
        generalize i+1 = k
        induction k with
        | zero => exact le_rfl
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact ih.trans (control_self_le f had.2 _)
      exact hmt.trans hg
    have hstep := (relativeDescentStep f mu (relativeState f lam mu t i)
      (by rw [← hstate i hi.le]; exact trajectory_below f _ hin.1 i) hmu hy
      (by rw [← hstate i hi.le, hnorm i hi.le, ← Function.iterate_succ_apply' f i t]; exact hbudget)).2
    have heq : (descentWith f)^[i+1] (countInitial lam t) =
        mu + relativeMaximum mu (actualLimitPart (relativeState f lam mu t i)) (f^[i+1] t) := by
      rw [Function.iterate_succ_apply', hstate i hi.le, hstep,
        ← hstate i hi.le, hnorm i hi.le, ← Function.iterate_succ_apply' f i t]
    change (descentWith f)^[i+1] (countInitial lam t) - mu = _
    rw [heq, Ordinal.add_sub_cancel]

end LogicLineages.PermittedControl
