module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierAdvanceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProof
open NormalForm PlainFrontier

theorem strictRankBound : PlainFrontierTargets.StrictRankBound := by
  intro n M s hb
  induction n with
  | zero => simpa only [run_zero, Nat.add_zero] using hb
  | succ n ih =>
      intro p hp
      rw [run_succ] at hp
      obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
      have hqbound := ih q hq
      have hdrop := PlainBranchSplitProof.strictFrontierDecrease q p hpq
      omega

theorem nonlinearNames_subset_variables (p : Formula) :
    PlainBranchProvenance.nonlinearNames p ⊆ p.variables.toFinset := by
  intro i hi
  obtain ⟨s, hs, rfl⟩ := (PlainBranchProvenanceProof.mem_nonlinearNames p i).mp hi
  have ho := ((PlainBranchProvenanceProof.mem_nonlinear p s).mp hs).1
  obtain ⟨a, ha, hs⟩ := List.mem_flatMap.mp ho
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
  exact List.mem_toFinset.mpr (MaximalPlainBranchProof.atom_name_mem p a ha b hb)

theorem literalFuelBound : PlainFrontierTargets.LiteralFuelBound := by
  intro p
  have h₁ := Finset.card_le_card (nonlinearNames_subset_variables p)
  have h₂ := List.toFinset_card_le p.variables
  change (PlainBranchProvenance.nonlinearNames p).card < p.variables.length + 1
  omega

theorem frontierExhaustion : PlainFrontierTargets.FrontierExhaustion := by
  intro p
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  have hb : ∀ r ∈ (initial p).2, (PlainBranchProvenance.nonlinearNames r).card ≤ p.variables.length := by
    intro r hr
    have he : r = p := List.mem_singleton.mp hr
    subst r
    have h := literalFuelBound p
    change (PlainBranchProvenance.nonlinearNames p).card < p.variables.length + 1 at h
    omega
  have h := strictRankBound (fuel p) p.variables.length (initial p) hb q hq
  unfold fuel at h
  omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProof
