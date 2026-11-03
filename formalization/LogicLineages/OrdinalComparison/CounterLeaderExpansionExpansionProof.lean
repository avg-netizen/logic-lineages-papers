module
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionTargets
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionSuppliersProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionEntriesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderExpansion.Proof

/-! The unsigned source blocks telescope in their original descending order.
The final passage to integers preserves the source's negative quadratic
correction, using a subtraction bound proved from the actual entry domains. -/

private theorem countExpansion (n c t : Nat) (ht : threshold n c ≤ t) :
    count (n+3) c t =
      leader n c t / 2 - (c+1)/2 + 1 + (residuals n c t).sum := by
  induction n generalizing t with
  | zero =>
    have hb := (block 1 c t (by simpa only [threshold] using ht)).1
    change count 3 c t =
      count 2 c (kernel 3 (c+3) t) + count 3 (c+3) t at hb
    have hq := quadraticCount c (kernel 3 (c+3) t) (by
      have hk := kernel_ge 3 (c+3) t
      dsimp only [threshold] at ht
      omega)
    change count 2 c (kernel 3 (c+3) t) =
      Phi (kernel 3 (c+3) t) / 2 - (c+1)/2 + 1 at hq
    rw [hq] at hb
    simpa only [Nat.zero_add, leader, leaderPreimage, bottomInput,
      residuals, entries, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero] using hb
  | succ n ih =>
    let u := kernel (n+4) (c+n+4) t
    have hu : t ≤ u := kernel_ge (n+4) (c+n+4) t
    have htail : threshold n c ≤ u := by
      dsimp only [threshold] at ht ⊢
      omega
    have hi := ih u htail
    have hb := (block (n+2) c t (by
      dsimp only [threshold] at ht
      omega)).1
    change count (n+4) c t =
      count (n+3) c u + count (n+4) (c+n+4) t at hb
    have hleader : leader (n+1) c t = leader n c u := rfl
    have hres : (residuals (n+1) c t).sum =
        count (n+4) (c+n+4) t + (residuals n c u).sum := by
      simp only [residuals, entries, List.map_cons, List.sum_cons, Nat.add_assoc, u]
    change count (n+4) c t = _
    rw [hleader, hres, hb, hi]
    omega

theorem exactCounterLeaderIdentity : Targets.ExactCounterLeaderIdentity := by
  intro n c t ht
  have hpre : t ≤ leaderPreimage n c t :=
    (exactEntryDomains n c t ht).2.2.2.1
  have hPhi : leaderPreimage n c t < leader n c t :=
    self_lt_Phi (leaderPreimage n c t)
  have hsub : (c+1)/2 ≤ leader n c t / 2 := by
    dsimp only [threshold] at ht
    omega
  refine ⟨phiEven (leaderPreimage n c t), hsub, ?_⟩
  have hc := countExpansion n c t ht
  omega

end LogicLineages.OrdinalComparison.CounterLeaderExpansion.Proof
