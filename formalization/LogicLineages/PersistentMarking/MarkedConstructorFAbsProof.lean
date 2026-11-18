import LogicLineages.PersistentMarking.MarkedConstructorTargets
namespace LogicLineages.PersistentMarking.MarkedConstructorFAbsProof
open Spine NameBridge DecisionPorts HereditaryDomainCode MarkedConstructorTargets

theorem fabs : MarkedConstructorTargets.FAbsExact := by
  intro E heads M p t
  cases ht : p.2.1 with
  | ground => cases t <;> simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht]
  | arrow σ τ =>
    cases t with
    | free ρ x => simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht]
    | bound ρ i => simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht]
    | head f ts => simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht]
    | marked f ρ bs es => simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht]
    | lam ρ body =>
      by_cases he : σ = ρ
      · subst ρ
        cases hi : ProtectedSpineEnvironment.openingSlot p.2.2.1 with
        | none => simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht,hi]
        | some i =>
          cases hc : StructuralActions.markedAction E heads M
              (MarkedConstructorTests.fabsParameter E p σ τ i) with
          | none => simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht,hi,hc]
          | some c =>
            simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht,hi,hc,
              MarkedConstructorTests.fabsParameter]
      · simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht,he]
end LogicLineages.PersistentMarking.MarkedConstructorFAbsProof
