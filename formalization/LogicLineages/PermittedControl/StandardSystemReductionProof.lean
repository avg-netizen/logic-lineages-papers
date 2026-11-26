module
public import LogicLineages.PermittedControl.StandardSystemAssemblyProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemBoundProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSystemMask.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open SelectedSystemReduction
open Source.FunctionalHardnessCompletion (System compileSystem strictSystemPair weakSystemPair)

 theorem systemEquality : StandardSystemMask.SystemEquality := by
  intro policy n s
  constructor
  · rintro ⟨ρ,hρ⟩
    obtain ⟨σ,hσ,he⟩ := (valuationPreservingSystem  policy n s ρ).mp hρ
    exact ⟨σ,(StandardAggregation.Proof.aggregateAt  policy σ _).2.2.2.1.mpr he⟩
  · rintro ⟨σ,he⟩
    let ρ := pullback Phi (compileSystem s).original σ
    refine ⟨ρ,(valuationPreservingSystem  policy n s ρ).mpr ?_⟩
    exact ⟨σ,(fun _ _ _ => rfl),
      (StandardAggregation.Proof.aggregateAt  policy σ _).2.2.2.1.mp he⟩

 theorem strictComplement 
    (policy : Policy) {n : Nat} (s : System n) :
    universalStrictSystem Phi policy s ↔
      ¬∃ ρ : AdmissibleSubstitution Phi (SignedPair.Context n), OrdinalSolves Phi s ρ := by
  constructor
  · intro hu hs
    obtain ⟨ρ,he⟩ := (systemEquality  policy n s).mp hs
    have hh := hu ρ
    omega
  · intro hn ρ
    have hne : groundValue Phi policy ρ (strictSystemPair s).1≠
        groundValue Phi policy ρ (strictSystemPair s).2 := by
      intro he
      exact hn ((systemEquality  policy n s).mpr ⟨ρ,he⟩)
    have hle := (StandardAggregation.Proof.aggregateAt  policy ρ
      (compileSystem s).detectors).2.2.1
    change groundValue _ _ _ (strictSystemPair s).2≤groundValue _ _ _ (strictSystemPair s).1 at hle
    omega

 theorem queryComplements : StandardSystemMask.QueryComplements := by
  intro policy n s
  refine ⟨strictComplement  policy s,?_⟩
  have he : universalWeakSystem Phi policy s ↔ universalStrictSystem Phi policy s := by
    apply forall_congr'
    intro ρ
    have h := StandardAggregation.Proof.aggregateWeakQuery  _ policy ρ
      (compileSystem s).detectors
    exact h.2.trans h.1.symm
  exact he.trans (strictComplement  policy s)

 theorem levelTwoBounds : StandardSystemMask.LevelTwoBounds :=
  FunctionalHardnessCompletion.SystemProof.levelTwoBounds

 theorem selectedSystemReduction : (ActualRenaming ∧ ValuationPreservingSystem ∧ SystemEquality ∧ QueryComplements ∧ LevelTwoBounds) :=
  ⟨actualRenaming,valuationPreservingSystem,systemEquality,queryComplements,levelTwoBounds⟩
end LogicLineages.PermittedControl.StandardSystemMask.Proof
