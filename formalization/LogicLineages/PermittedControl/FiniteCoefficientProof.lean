module
public import LogicLineages.PermittedControl.FiniteCoefficientTargets
public import LogicLineages.PermittedControl.TerminalProof
public import LogicLineages.OrdinalComparison.SmallKernelSuppliersProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

theorem terminal_count_agreement (f : Nat → Nat) (a : Ordinal) (ha : a < epsilonZero) :
    (terminalWith f a).2 = actualControlledCount f a := by
  revert ha
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha
    by_cases hfin : a < Ordinal.omega0
    · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hfin
      rw [terminal_finite f n, (actualControlledCountRecursion f _ ha).1 (Ordinal.natCast_lt_omega0 n)]
    · have hn := le_of_not_gt hfin
      have hd := descent_strict f a hn ha
      have hi := ih (descentWith f a) hd (hd.trans ha)
      rw [(terminal_nonfinite f a ha hn).2, hi, (actualControlledCountRecursion f a ha).2 hn]
      rfl

theorem finiteCoefficient_below (k n : Nat) :
    Ordinal.omega0 * (k : Ordinal) + (n : Ordinal) < epsilonZero := by
  have hb : Ordinal.omega0 * (k : Ordinal) < epsilonZero := by
    simpa only [Nat.cast_one, Ordinal.opow_one] using (actualFiniteMonomialFacts 1 k).1
  exact (actualFiniteTailClosureNorm _ hb n).1

theorem finiteCoefficientTerminal : Targets.FiniteCoefficientTerminal := by
  intro f hmono hf k n
  have ha := finiteCoefficient_below k n
  have hc : (terminalWith f (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))).2 = k := by
    rw [terminal_count_agreement f _ ha]
    exact actualExpansiveControlLinearCount f (control_self_le f hf) k n
  have hz := (terminal_identities f hmono hf _ ha).2
  rw [hc, actualFiniteHeadNorm] at hz
  exact ⟨hc, hz⟩

theorem finiteCoefficient : Targets.FiniteCoefficient := by
  intro f hmono hf k n
  have ht := finiteCoefficientTerminal f hmono hf k n
  have hv := (terminal_identities f hmono hf _ (finiteCoefficient_below k n)).1
  rw [ht.1, ht.2] at hv
  exact hv

theorem selectedFiniteCoefficient : Targets.SelectedFiniteCoefficient := by
  intro f hf k n
  have had := selected_admissibility f hf
  exact ⟨finiteCoefficient f had.1 had.2 k n, finiteCoefficientTerminal f had.1 had.2 k n⟩

end LogicLineages.PermittedControl
