module
public import LogicLineages.PermittedControl.StandardSeededSystemAssemblyProof
public import LogicLineages.PermittedControl.StandardAggregationWeakProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemBoundProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSeededSystem.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion
open SelectedSystemReduction
open SelectedSeededSystem (Solves universalStrict universalWeak)

theorem systemEquality : StandardSeededSystem.SystemEquality := by
  intro policy n s
  constructor
  · intro hp
    obtain ⟨ρ,hρ⟩ := (StandardSeededCompiler.Proof.simultaneousSolvability n s).mp hp
    obtain ⟨σ,hσ,he⟩ := (valuationPreservation policy n s ρ).mp hρ
    exact ⟨σ,(StandardAggregation.Proof.aggregateAt policy σ _).2.2.2.1.mpr he⟩
  · rintro ⟨σ,he⟩
    let ρ := pullback Phi (SeededSystem.compile s).original σ
    apply (StandardSeededCompiler.Proof.simultaneousSolvability n s).mpr
    refine ⟨ρ,(valuationPreservation policy n s ρ).mpr ?_⟩
    exact ⟨σ,(fun _ _ _ => rfl),
      (StandardAggregation.Proof.aggregateAt policy σ _).2.2.2.1.mp he⟩

theorem strictComplement (policy : Policy) {n : Nat} (s : System n) :
    universalStrict Phi policy s ↔ ¬PolynomialSatisfiable s := by
  constructor
  · intro hu hs
    obtain ⟨ρ,he⟩ := (systemEquality policy n s).mp hs
    have hh := hu ρ
    omega
  · intro hn ρ
    have hne : groundValue Phi policy ρ (SeededSystem.strictPair s).1≠
        groundValue Phi policy ρ (SeededSystem.strictPair s).2 := by
      intro he
      exact hn ((systemEquality policy n s).mpr ⟨ρ,he⟩)
    have hle := (StandardAggregation.Proof.aggregateAt policy ρ
      (SeededSystem.compile s).detectors).2.2.1
    change groundValue _ _ _ (SeededSystem.strictPair s).2≤groundValue _ _ _ (SeededSystem.strictPair s).1 at hle
    omega

theorem queryComplements : StandardSeededSystem.QueryComplements := by
  intro policy n s
  refine ⟨strictComplement policy s,?_⟩
  have he : universalWeak Phi policy s ↔ universalStrict Phi policy s := by
    apply forall_congr'
    intro ρ
    have h := StandardAggregation.Proof.aggregateWeakQuery _ policy ρ
      (SeededSystem.compile s).detectors
    exact h.2.trans h.1.symm
  exact he.trans (strictComplement policy s)

theorem levelThreeBounds : StandardSeededSystem.LevelThreeBounds :=
  SeededSystem.Proof.exactLevelThreeBounds

theorem successfulQueries : StandardSeededSystem.SuccessfulQueries := by
  intro policy n s ρ
  have h := StandardAggregation.Proof.aggregateAt policy ρ (SeededSystem.compile s).detectors
  exact ⟨h.1,h.2.1,StandardAggregation.Proof.groundResult policy ρ _,
    StandardAggregation.Proof.groundResult policy ρ _⟩
end LogicLineages.PermittedControl.StandardSeededSystem.Proof
