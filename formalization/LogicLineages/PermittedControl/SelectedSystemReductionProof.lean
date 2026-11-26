module
public import LogicLineages.PermittedControl.SelectedSystemAssemblyProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemBoundProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSystemReduction.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion (System compileSystem strictSystemPair weakSystemPair)

 theorem systemEquality : SelectedSystemReductionTargets.SystemEquality := by
  intro ctrl K hc policy n s
  constructor
  · rintro ⟨ρ,hρ⟩
    obtain ⟨σ,hσ,he⟩ := (valuationPreservingSystem ctrl K hc policy n s ρ).mp hρ
    exact ⟨σ,(SelectedAggregation.Proof.aggregateAt ctrl K hc policy σ _).2.2.2.1.mpr he⟩
  · rintro ⟨σ,he⟩
    let ρ := pullback ctrl (compileSystem s).original σ
    refine ⟨ρ,(valuationPreservingSystem ctrl K hc policy n s ρ).mpr ?_⟩
    exact ⟨σ,(fun _ _ _ => rfl),
      (SelectedAggregation.Proof.aggregateAt ctrl K hc policy σ _).2.2.2.1.mp he⟩

 theorem strictComplement (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) {n : Nat} (s : System n) :
    universalStrictSystem ctrl policy s ↔
      ¬∃ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n), OrdinalSolves ctrl s ρ := by
  constructor
  · intro hu hs
    obtain ⟨ρ,he⟩ := (systemEquality ctrl K hc policy n s).mp hs
    have hh := hu ρ
    omega
  · intro hn ρ
    have hne : groundValue ctrl policy ρ (strictSystemPair s).1≠
        groundValue ctrl policy ρ (strictSystemPair s).2 := by
      intro he
      exact hn ((systemEquality ctrl K hc policy n s).mpr ⟨ρ,he⟩)
    have hle := (SelectedAggregation.Proof.aggregateAt ctrl K hc policy ρ
      (compileSystem s).detectors).2.2.1
    change groundValue _ _ _ (strictSystemPair s).2≤groundValue _ _ _ (strictSystemPair s).1 at hle
    omega

 theorem queryComplements : SelectedSystemReductionTargets.QueryComplements := by
  intro ctrl K hc policy n s
  refine ⟨strictComplement ctrl K hc policy s,?_⟩
  have he : universalWeakSystem ctrl policy s ↔ universalStrictSystem ctrl policy s := by
    apply forall_congr'
    intro ρ
    have h := SelectedAggregation.Proof.aggregateWeakQuery ctrl K hc _ policy ρ
      (compileSystem s).detectors
    exact h.2.trans h.1.symm
  exact he.trans (strictComplement ctrl K hc policy s)

 theorem levelTwoBounds : SelectedSystemReductionTargets.LevelTwoBounds :=
  FunctionalHardnessCompletion.SystemProof.levelTwoBounds

 theorem selectedSystemReduction : SelectedSystemReductionTargets.SelectedSystemReduction :=
  ⟨actualRenaming,valuationPreservingSystem,systemEquality,queryComplements,levelTwoBounds⟩
end LogicLineages.PermittedControl.SelectedSystemReduction.Proof
