import LogicLineages.PersistentMarking.MarkedConstructorWeakOrderProof
import LogicLineages.PersistentMarking.MarkedConstructorFAbsOrderProof
import LogicLineages.PersistentMarking.MarkedConstructorValidityProof

namespace LogicLineages.PersistentMarking.MarkedConstructorFamilyOrderProof
open Spine DecisionPorts
open MarkedFamilyCoherence (weakenParameter)

theorem familyMonotone : MarkedConstructorTargets.FamilyMonotone := by
  intro S E heads M N p hpfx hm hn hp hmn Δ hΔ he
  let a := weakenParameter E p Δ
  have ha := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hΔ he
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro t _
    have hw := MarkedConstructorWeakOrderProof.weakOrder S E heads M N a a t ha ha rfl rfl rfl
      (MarkedConstructorOwnerOrderProof.ownerFamilyOrder E heads M N a hm hn hmn)
      (MarkedConstructorSelectOrderProof.tagsInputOrder E heads a a ha ha
        (MarkedConstructorValidityProof.inputReflexive E heads a ha))
      (fun _ h => h)
      (MarkedConstructorFAbsOrderProof.familyOrder E heads M N a t hm hn hmn)
    exact ⟨hw,hw⟩
  · intro ds τ hpre xs hx
    obtain ⟨u,hu,_,hU⟩ := MarkedConstructorTupleProof.tupleSuccess S E heads M p Δ ds τ xs hpfx hm hp hΔ he hpre hx
    obtain ⟨v,hv,_,hV⟩ := MarkedConstructorTupleProof.tupleSuccess S E heads N p Δ ds τ xs hpfx hn hp hΔ he hpre hx
    let q := MarkedConstructorAppendProof.appendParameter E a τ ds xs
    obtain ⟨v',hv',_,hle⟩ := MarkedConstructorLookupProof.actionOrder E heads M N q u hm hn hmn hu
    have hvq : StructuralActions.markedAction E heads N q = some v := hv
    have hvv' := Option.some.inj (hvq.symm.trans hv')
    rw [hU,hV,hvv']
    exact hle

theorem exact_FamilyMonotone : MarkedConstructorTargets.FamilyMonotone := familyMonotone
#print axioms exact_FamilyMonotone
end LogicLineages.PersistentMarking.MarkedConstructorFamilyOrderProof
