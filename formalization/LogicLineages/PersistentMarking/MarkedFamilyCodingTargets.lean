import LogicLineages.PersistentMarking.MarkedFamilyCoding
namespace LogicLineages.PersistentMarking.MarkedFamilyCodingTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding

def RawEnumeration : Prop := ∀ E heads c, c ∈ MarkedFamilyCoding.rawCodes E heads ↔ FitsFamily E heads c

def CoordinateSuccess : Prop := ∀ E heads c p, FitsFamily E heads c →
  MarkedFamilyParameters.Valid E heads p → ∃ i,
    MarkedFamilyCoding.lookup (MarkedFamilyParameters.schema E heads) c p = some i ∧
    i < ((descriptor E p.2.1).carriers p.2.2.1).length

def OutputSuccess : Prop := ∀ E heads c p, FitsFamily E heads c →
  MarkedFamilyParameters.Valid E heads p → ∃ v,
    output E heads c p = some v ∧ v ∈ (descriptor E p.2.1).carriers p.2.2.1

def EncodingExact : Prop := ∀ E heads v,
  OutputsValid E heads v ↔ ∃ c, MarkedFamilyCoding.encode E heads v = some c ∧ FitsFamily E heads c

def CodeRoundtrip : Prop := ∀ E heads c, FitsFamily E heads c →
  MarkedFamilyCoding.encode E heads (MarkedFamilyCoding.decode E heads c) = some c

def SemanticRoundtrip : Prop := ∀ E heads v c, OutputsValid E heads v →
  MarkedFamilyCoding.encode E heads v = some c →
  FamilyEq E heads (MarkedFamilyCoding.decode E heads c) v

def EncodingCongruence : Prop := ∀ E heads v w, FamilyEq E heads v w →
  MarkedFamilyCoding.encode E heads v = MarkedFamilyCoding.encode E heads w
end LogicLineages.PersistentMarking.MarkedFamilyCodingTargets
