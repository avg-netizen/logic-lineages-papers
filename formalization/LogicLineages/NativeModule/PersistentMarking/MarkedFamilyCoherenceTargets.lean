module

public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyCoherence

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedFamilyCoherenceTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

def InputOrderExact : Prop := ∀ E heads p q,
  MarkedFamilyParameters.Valid E heads p → MarkedFamilyParameters.Valid E heads q →
  (MarkedFamilyCoherence.inputLe E p q = true ↔ MarkedFamilyCoherence.InputLE E p q)

def DestinationValid : Prop := ∀ E heads p Δ,
  MarkedFamilyParameters.Valid E heads p → WellFormed E.types E.ports Δ → Extends p.2.2.1 Δ →
  MarkedFamilyParameters.Valid E heads (MarkedFamilyCoherence.weakenParameter E p Δ)

def MonotoneExact : Prop := ∀ E heads c, FitsFamily E heads c →
  (MarkedFamilyCoherence.monotoneBool E heads c = true ↔
    MarkedFamilyCoherence.Monotone E heads (MarkedFamilyCoding.decode E heads c))

def CoherentExact : Prop := ∀ E heads c, FitsFamily E heads c →
  (MarkedFamilyCoherence.coherentBool E heads c = true ↔
    MarkedFamilyCoherence.Coherent E heads (MarkedFamilyCoding.decode E heads c))

def RetentionExact : Prop := ∀ E heads c,
  c ∈ MarkedFamilyCoherence.retained E heads ↔ FitsFamily E heads c ∧
    MarkedFamilyCoherence.ValidFamily E heads (MarkedFamilyCoding.decode E heads c)

def EncodingComplete : Prop := ∀ E heads v,
  MarkedFamilyCoherence.ValidFamily E heads v → ∃ c,
    MarkedFamilyCoding.encode E heads v = some c ∧ c ∈ MarkedFamilyCoherence.retained E heads ∧
    FamilyEq E heads (MarkedFamilyCoding.decode E heads c) v
end LogicLineages.PersistentMarking.MarkedFamilyCoherenceTargets
