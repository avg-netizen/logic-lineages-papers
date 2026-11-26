import LogicLineages.PersistentMarking.MarkedConstructorTargets
namespace LogicLineages.PersistentMarking.MarkedConstructorFAbsExactProof
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
            have hTest : MarkedConstructorTests.fabsTest E heads M p (.lam σ body) =
                (HereditaryDomainSemantics.decode E τ
                  (ProtectedSpineEnvironment.openingContext p.2.2.1 σ i) c).weak
                  (ProtectedSpineEnvironment.openingContext p.2.2.1 σ i)
                  (openBody σ (portName E.names i) body) := by
              simp only [MarkedConstructorTests.fabsTest, ht, if_pos rfl, hi, hc]
            rw [hTest]
            constructor
            · intro h
              exact ⟨σ, τ, body, i, c, ht, rfl, hi, hc, h⟩
            · rintro ⟨ρ, υ, q, j, v, hty, hlam, hj, hv, h⟩
              cases ht.symm.trans hty
              cases hlam
              cases hi.symm.trans hj
              cases hc.symm.trans hv
              exact h
      · simp [MarkedConstructorTests.fabsTest,FAbsWitness,ht,he,Ne.symm he]
end LogicLineages.PersistentMarking.MarkedConstructorFAbsExactProof
