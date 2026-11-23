module

public import LogicLineages.NativeModule.PersistentMarking.MarkedBaseTupleTargets
public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceBasicProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedBaseHeadCoverageProof
open Spine NameBridge DecisionPorts DecisionInventory DecisionSourceUniverse FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedBaseTuples

theorem declaration : MarkedBaseTupleTargets.HeadDeclaration := DecisionInventoryProof.declarations

theorem coverage : MarkedBaseTupleTargets.SourceHeadCoverage := by
  intro s t σ τ hs ht hos hot f hf
  have hu := (DecisionSourceBasicProof.initial s t σ τ hs ht hos hot).2
  have hd : ∀ ρ, ρ ∈ DecisionInventory.declaration f → ρ ∈ (inventory s t).types :=
    fun ρ hρ => hu.1 ρ (declaration s f hf ρ hρ)
  constructor
  · exact hd f.result (List.mem_append_left _ (DecisionSourceBasicProof.subtypeSelf f.result))
  · intro ρ hρ
    exact hd ρ (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨ρ,hρ,DecisionSourceBasicProof.subtypeSelf ρ⟩))
end LogicLineages.PersistentMarking.MarkedBaseHeadCoverageProof
