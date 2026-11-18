module
public import LogicLineages.PermittedControl.InitialLowDivergenceProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem initial_pass_swap (mu nu delta : Ordinal.{0}) :
    initialPeelingPass mu nu delta → initialPeelingPass nu mu delta := by
  intro h
  rcases h with h | h | ⟨hadj,hex⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h)
  · right; right
    refine ⟨hadj.symm,?_⟩
    simpa only [min_comm] using hex

 theorem initial_ordered_divergence (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu delta A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hd : delta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hdl : Order.IsSuccLimit delta)
    (ht : thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t)
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hc : relativeProfile mu (Ordinal.log Ordinal.omega0 delta)<relativeProfile nu (Ordinal.log Ordinal.omega0 delta))
    (hfail : ¬ initialPeelingPass mu nu delta) :
    Targets.OrientedUnitDivergence f mu nu (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) A A' := by
  by_cases hh : ∃ e ∈ initialPeelingUnits delta, (2 : Ordinal) < e
  · exact initial_high_divergence f B hf mu nu delta A A' t hmu hnu hd hA hA' hmud hnud hdl ht hpart hpart' hN hN' hc hh
  · have hlow : ∀ e ∈ initialPeelingUnits delta, e ≤ 2 := by
      intro e he
      exact le_of_not_gt (fun hg => hh ⟨e,he,hg⟩)
    exact initial_low_divergence f B hf mu nu delta A A' t hmu hnu hd hA hA' hmud hnud hdl ht hpart hpart' hN hN' hc hlow hfail

 theorem actualInitialPeeling : Targets.ActualInitialPeeling := by
  intro f B hf mu nu delta A A' t hmu hnu hd hA hA' hmud hnud hdl ht hpart hpart' hN hN'
  constructor
  · exact initial_pass_return f B hf mu nu delta A A' t hmu hnu hd hA hA' hmud hnud hdl ht hpart hpart' hN hN'
  · intro hfail
    have hne : relativeProfile mu (Ordinal.log Ordinal.omega0 delta) ≠ relativeProfile nu (Ordinal.log Ordinal.omega0 delta) :=
      fun h => hfail (Or.inl h)
    rcases lt_or_gt_of_ne hne with hc | hc
    · obtain ⟨i,hi,hkeep,hkeep'⟩ := initial_ordered_divergence f B hf mu nu delta A A' t hmu hnu hd hA hA' hmud hnud hdl ht hpart hpart' hN hN' hc hfail
      exact ⟨i,hi.ne', (compare_gt_iff_gt.mpr hi).trans (compare_gt_iff_gt.mpr hc).symm,hkeep',hkeep⟩
    · have ht' : thickBlockTail (initialPeelingRadius nu mu delta) B ≤ t := by
        have hr : initialPeelingRadius nu mu delta=initialPeelingRadius mu nu delta := by
          dsimp [initialPeelingRadius]
          omega
        rwa [hr]
      have hfail' : ¬ initialPeelingPass nu mu delta := fun h => hfail (initial_pass_swap nu mu delta h)
      obtain ⟨i,hi,hkeep,hkeep'⟩ := initial_ordered_divergence f B hf nu mu delta A' A t hnu hmu hd hA' hA hnud hmud hdl ht' hpart' hpart hN' hN hc hfail'
      exact ⟨i,hi.ne, (compare_lt_iff_lt.mpr hi).trans (compare_lt_iff_lt.mpr hc).symm,hkeep,hkeep'⟩

end LogicLineages.PermittedControl
