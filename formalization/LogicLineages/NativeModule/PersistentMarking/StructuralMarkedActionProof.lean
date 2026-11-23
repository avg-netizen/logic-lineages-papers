module

public import LogicLineages.NativeModule.PersistentMarking.StructuralActionTargets
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyRetentionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralMarkedActionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem sound : StructuralActionTargets.MarkedActionSound := by
  intro E heads c p hc hp
  exact MarkedFamilyLookupProof.outputSuccess E heads c p
    ((MarkedFamilyRetentionProof.retentionExact E heads c).mp hc).1 hp

theorem decoded (E : Environment) (heads : List Head) (c : Code) (p : MarkedFamilyParameters.Parameter) (v : Code)
    (hv : StructuralActions.markedAction E heads c p = some v) : MarkedFamilyCoding.decode E heads c p = v := by
  simp only [MarkedFamilyCoding.decode,StructuralActions.markedAction] at hv ⊢
  rw [hv]; rfl

theorem laws : StructuralActionTargets.MarkedActionLaws := by
  intro E heads c hc
  have hvalid := ((MarkedFamilyRetentionProof.retentionExact E heads c).mp hc).2
  constructor
  · intro p q a b hp hq hle ha hb
    have h := hvalid.2.1 p q hp hq hle
    rw [decoded E heads c p a ha,decoded E heads c q b hb] at h
    exact h
  · intro p Δ a b hp hw he ha hb
    have h := hvalid.2.2 p hp Δ hw he
    rw [decoded E heads c p a ha,decoded E heads c (MarkedFamilyCoherence.weakenParameter E p Δ) b hb] at h
    exact h
end LogicLineages.PersistentMarking.StructuralMarkedActionProof
