module
public import LogicLineages.OrdinalComparison.CounterUnequalLeaderOrderGrowthProof
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsGrowthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterUnequalLeaderOrder.Proof
open CounterLeaderExpansion

private theorem ordered (n m c e t u : Nat)
    (ht : CounterLeaderBounds.threshold n c ≤ t)
    (hu : CounterLeaderBounds.threshold m e ≤ u)
    (hh : leader n c t < leader m e u) :
    count (n+3) c t < count (m+3) e u := by
  have hg := actualLeaderGap n m c e t u hh
  have hg' : 2 * 2^(leader n c t) ≤ leader m e u := by
    simpa only [pow_succ, Nat.mul_comm] using hg
  have hp : leader n c t < 2^(leader n c t) := Nat.lt_two_pow_self
  have h1 := (CounterLeaderBounds.Proof.strictActualLeaderBounds n c t ht).2
  have h2 := (CounterLeaderBounds.Proof.strictActualLeaderBounds m e u hu).1
  omega

theorem actualUnequalLeaderOrder : Targets.ActualUnequalLeaderOrder := by
  intro n m c e t u ht hu hne
  rcases lt_or_gt_of_ne hne with hh | hh
  · have hc := ordered n m c e t u ht hu hh
    exact ⟨⟨fun _ => hh, fun _ => hc⟩, ne_of_lt hc⟩
  · have hc := ordered m n e c u t hu ht hh
    exact ⟨⟨fun h => False.elim ((not_lt_of_gt hc) h),
      fun h => False.elim ((not_lt_of_gt hh) h)⟩, ne_of_gt hc⟩

end LogicLineages.OrdinalComparison.CounterUnequalLeaderOrder.Proof
