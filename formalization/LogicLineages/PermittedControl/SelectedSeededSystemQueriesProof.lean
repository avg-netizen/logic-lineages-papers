module
public import LogicLineages.PermittedControl.SelectedSeededSystemAssemblyProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemBoundProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededSystem.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion
open SelectedSystemReduction

 theorem systemEquality : SelectedSeededSystemTargets.SystemEquality := by
  intro ctrl K hc policy n s
  constructor
  · intro hp
    obtain ⟨ρ,hρ⟩ := (SelectedSeededCompiler.Proof.simultaneousSolvability ctrl K hc n s).mp hp
    obtain ⟨σ,hσ,he⟩ := (valuationPreservingSystem ctrl K hc policy n s ρ).mp hρ
    exact ⟨σ,(SelectedAggregation.Proof.aggregateAt ctrl K hc policy σ _).2.2.2.1.mpr he⟩
  · rintro ⟨σ,he⟩
    let ρ := pullback ctrl (SeededSystem.compile s).original σ
    apply (SelectedSeededCompiler.Proof.simultaneousSolvability ctrl K hc n s).mpr
    refine ⟨ρ,(valuationPreservingSystem ctrl K hc policy n s ρ).mpr ?_⟩
    exact ⟨σ,(fun _ _ _ => rfl),
      (SelectedAggregation.Proof.aggregateAt ctrl K hc policy σ _).2.2.2.1.mp he⟩

 theorem strictComplement (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) {n : Nat} (s : System n) :
    universalStrict ctrl policy s ↔
      ¬PolynomialSatisfiable s := by
  constructor
  · intro hu hs
    obtain ⟨ρ,he⟩ := (systemEquality ctrl K hc policy n s).mp hs
    have hh := hu ρ
    omega
  · intro hn ρ
    have hne : groundValue ctrl policy ρ (SeededSystem.strictPair s).1≠
        groundValue ctrl policy ρ (SeededSystem.strictPair s).2 := by
      intro he
      exact hn ((systemEquality ctrl K hc policy n s).mpr ⟨ρ,he⟩)
    have hle := (SelectedAggregation.Proof.aggregateAt ctrl K hc policy ρ
      (SeededSystem.compile s).detectors).2.2.1
    change groundValue _ _ _ (SeededSystem.strictPair s).2≤groundValue _ _ _ (SeededSystem.strictPair s).1 at hle
    omega

 theorem queryComplements : SelectedSeededSystemTargets.QueryComplements := by
  intro ctrl K hc policy n s
  refine ⟨strictComplement ctrl K hc policy s,?_⟩
  have he : universalWeak ctrl policy s ↔ universalStrict ctrl policy s := by
    apply forall_congr'
    intro ρ
    have h := SelectedAggregation.Proof.aggregateWeakQuery ctrl K hc _ policy ρ
      (SeededSystem.compile s).detectors
    exact h.2.trans h.1.symm
  exact he.trans (strictComplement ctrl K hc policy s)

 theorem levelThreeBounds : SelectedSeededSystemTargets.LevelThreeBounds :=
  SeededSystem.Proof.exactLevelThreeBounds

 theorem successfulQueries : SelectedSeededSystemTargets.SuccessfulQueries := by
  intro ctrl K hc policy n s ρ
  have h := SelectedAggregation.Proof.aggregateAt ctrl K hc policy ρ (SeededSystem.compile s).detectors
  refine ⟨h.1,h.2.1,?_,?_⟩
  all_goals
    obtain ⟨v,hv,he,hpos⟩ := SelectedFunctionalDetector.Proof.ground_facts ctrl K hc policy _ ρ
    exact ⟨v,hv,he,hpos⟩

end LogicLineages.PermittedControl.SelectedSeededSystem.Proof
