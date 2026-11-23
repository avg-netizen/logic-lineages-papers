module

public import LogicLineages.NativeModule.PersistentMarking.StructuralActionTargets
public import LogicLineages.NativeModule.PersistentMarking.MarkedBaseTupleRestrictionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralFullActionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem sound : StructuralActionTargets.FullActionSound := by
  intro E σ Γ c ds τ xs hw hc hp hx
  exact (HereditaryDecodedValidityProof.valid E σ Γ c hw hc).1 Γ hw (DecisionPortsProof.extensionRefl Γ) ds τ hp xs hx

theorem monotone : StructuralActionTargets.FullActionMonotone := by
  intro E σ Γ c d ds τ xs ys hw hc hd hcd hp hx hy hxy
  have hv := HereditaryDecodedValidityProof.valid E σ Γ d hw hd
  have hfun := ((HereditaryCodeOrderProof.exactOrder E σ Γ c d hw hc hd).mp hcd Γ hw
    (DecisionPortsProof.extensionRefl Γ)).2.2 ds τ hp xs hx
  have harg := hv.2.1 Γ hw (DecisionPortsProof.extensionRefl Γ) ds τ hp xs ys hx hy hxy
  exact (HereditaryPartialOrderProof.partialOrder E τ Γ hw).2.1 _ _ _
    (sound E σ Γ c ds τ xs hw hc hp hx) (sound E σ Γ d ds τ xs hw hd hp hx)
    (sound E σ Γ d ds τ ys hw hd hp hy) hfun harg

theorem natural : StructuralActionTargets.FullActionNatural := by
  intro E σ Γ Δ c ds τ xs hw hd he hc hp hx
  have hn := (HereditaryDecodedValidityProof.valid E σ Γ c hw hc).2.2 Γ Δ hw hd
    (DecisionPortsProof.extensionRefl Γ) he ds τ hp xs hx
  have hx' : TupleValues E Δ ds (HereditaryDomainSemantics.restrictValues E Γ Δ ds xs) :=
    MarkedBaseTupleRestrictionProof.restriction E Γ Δ ds xs hw hd he hx
  have hrest := ((HereditaryRestrictionProof.restriction E σ Γ Δ hw hd he c hc).2 Δ hd
    (DecisionPortsProof.extensionRefl Δ)).2.2 ds τ hp _ hx'
  exact hn.trans hrest.symm
end LogicLineages.PersistentMarking.StructuralFullActionProof
