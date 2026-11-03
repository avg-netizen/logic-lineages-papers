module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxBoundsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxFiniteProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof
open BalancedSyntax

theorem exactSmallBranchRepresentative : Targets.ExactSmallBranchRepresentative := by
  intro k Γ C E F ν hC hpositive hsmall
  let support := sourceSupport k Γ C E F
  let word := support.map ν
  let μ := boxValuation k Γ C E F word
  have hbounds := actualSmallInputBounds k Γ C E F ν hC hsmall
  obtain ⟨hwords, hempty, hagreement, houtside, hvalid⟩ := exactFiniteBox
  have hs (i : Nat) : i ∈ support ↔ i ∈ sourceAmbient k Γ C E F := by
    simp only [support, sourceSupport, List.mem_dedup]
  have hword : word ∈ singleCoreBoxWords (originalThreshold E F) support.length := by
    apply (hwords _ _ _).mpr
    refine ⟨List.length_map ν, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact ⟨hpositive i ((hs i).mp hi), hbounds.2.2.2 i ((hs i).mp hi)⟩
  have hagree : ∀ i ∈ sourceAmbient k Γ C E F, μ i = ν i := by
    intro i hi
    exact hagreement support ν i ((hs i).mpr hi)
  have hstable := actualSourceSupportStability k Γ C E F μ ν hagree
  have hμsmall : smallBranch k Γ C E F μ := by
    obtain ⟨a, ha, hlt⟩ := hsmall
    have hm : BalancedRow.input (basisValues k Γ C ν) a.2 ∈
        completeInputs k Γ C E F ν := List.mem_map.mpr ⟨a, ha, rfl⟩
    rw [← hstable.2.2.1] at hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact ⟨b, hb, lt_of_eq_of_lt he hlt⟩
  refine ⟨word, rfl, hword, hagree, (hvalid _ _ _ hword).1, ?_,
    hstable.1, hstable.2.1, hstable.2.2.1, hμsmall⟩
  intro i hi
  exact houtside support word (List.length_map ν) i (fun hm => hi ((hs i).mp hm))

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof
