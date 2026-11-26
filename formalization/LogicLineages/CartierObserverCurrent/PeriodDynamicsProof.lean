module
public import LogicLineages.CartierObserverCurrent.PeriodDynamicsTargets
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public meta import LogicLineages.Audit
@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodDynamics

theorem exactPeriodFromExclusions : Targets.ExactPeriodFromExclusions.{u} := by
  intro α f x r hr hup hmid hsmall
  have hn : 0 < 2 * r := by omega
  have hp : Function.IsPeriodicPt f (2 * r) x := hup
  let s := Function.minimalPeriod f x
  have hspos : 0 < s := hp.minimalPeriod_pos hn
  have hsdiv : s ∣ 2 * r := hp.minimalPeriod_dvd
  have hper : f^[s] x = x := Function.iterate_minimalPeriod
  have hne : s ≠ r := by intro h; apply hmid; simpa only [h] using hper
  change s = _
  by_contra hfull
  have hs : 3 * s ≤ 2 * r := by
    obtain ⟨k, hk⟩ := hsdiv
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> simp_all <;> omega
    nlinarith
  exact hsmall s hspos hs hper

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodDynamics
end LogicLineages.CartierObserverCurrent.PeriodDynamics
