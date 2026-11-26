module

public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyLattice

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedFamilyLatticeTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

def OrderExact : Prop := ∀ E heads a b,
  a ∈ MarkedFamilyCoherence.retained E heads → b ∈ MarkedFamilyCoherence.retained E heads →
  (MarkedFamilyLattice.le E heads a b = true ↔ MarkedFamilyLattice.SemanticLE E heads
    (MarkedFamilyCoding.decode E heads a) (MarkedFamilyCoding.decode E heads b))

def PartialOrder : Prop := ∀ E heads,
  (∀ a, a ∈ MarkedFamilyCoherence.retained E heads → MarkedFamilyLattice.le E heads a a = true) ∧
  (∀ a b c, a ∈ MarkedFamilyCoherence.retained E heads → b ∈ MarkedFamilyCoherence.retained E heads →
    c ∈ MarkedFamilyCoherence.retained E heads → MarkedFamilyLattice.le E heads a b = true →
    MarkedFamilyLattice.le E heads b c = true → MarkedFamilyLattice.le E heads a c = true) ∧
  (∀ a b, a ∈ MarkedFamilyCoherence.retained E heads → b ∈ MarkedFamilyCoherence.retained E heads →
    MarkedFamilyLattice.le E heads a b = true → MarkedFamilyLattice.le E heads b a = true → a=b)

def AggregateValid : Prop := ∀ (isMeet : Bool) E heads cs,
  (∀ c, c ∈ cs → c ∈ MarkedFamilyCoherence.retained E heads) →
  MarkedFamilyCoherence.ValidFamily E heads (MarkedFamilyLattice.aggregate isMeet E heads cs)

def CombineSuccess : Prop := ∀ (isMeet : Bool) E heads cs,
  (∀ c, c ∈ cs → c ∈ MarkedFamilyCoherence.retained E heads) →
  MarkedFamilyCoding.encode E heads (MarkedFamilyLattice.aggregate isMeet E heads cs) =
    some (MarkedFamilyLattice.combine isMeet E heads cs) ∧
  MarkedFamilyLattice.combine isMeet E heads cs ∈ MarkedFamilyCoherence.retained E heads ∧
  FamilyEq E heads (MarkedFamilyCoding.decode E heads (MarkedFamilyLattice.combine isMeet E heads cs))
    (MarkedFamilyLattice.aggregate isMeet E heads cs)

def Join : Prop := ∀ E heads cs,
  (∀ c, c ∈ cs → c ∈ MarkedFamilyCoherence.retained E heads) →
  MarkedFamilyLattice.join E heads cs ∈ MarkedFamilyCoherence.retained E heads ∧
  (∀ c, c ∈ cs → MarkedFamilyLattice.le E heads c (MarkedFamilyLattice.join E heads cs) = true) ∧
  (∀ b, b ∈ MarkedFamilyCoherence.retained E heads →
    (∀ c, c ∈ cs → MarkedFamilyLattice.le E heads c b = true) →
    MarkedFamilyLattice.le E heads (MarkedFamilyLattice.join E heads cs) b = true)

def Meet : Prop := ∀ E heads cs,
  (∀ c, c ∈ cs → c ∈ MarkedFamilyCoherence.retained E heads) →
  MarkedFamilyLattice.meet E heads cs ∈ MarkedFamilyCoherence.retained E heads ∧
  (∀ c, c ∈ cs → MarkedFamilyLattice.le E heads (MarkedFamilyLattice.meet E heads cs) c = true) ∧
  (∀ b, b ∈ MarkedFamilyCoherence.retained E heads →
    (∀ c, c ∈ cs → MarkedFamilyLattice.le E heads b c = true) →
    MarkedFamilyLattice.le E heads b (MarkedFamilyLattice.meet E heads cs) = true)

def FiniteNonempty : Prop := ∀ E heads,
  (MarkedFamilyCoherence.retained E heads).Pairwise (· ≠ ·) ∧ ∃ c, c ∈ MarkedFamilyCoherence.retained E heads

def Complete : Prop := ∀ E heads (P : Code → Prop),
  ∃ sup inf, sup ∈ MarkedFamilyCoherence.retained E heads ∧ inf ∈ MarkedFamilyCoherence.retained E heads ∧
  (∀ c, c ∈ MarkedFamilyCoherence.retained E heads → P c → MarkedFamilyLattice.le E heads c sup = true) ∧
  (∀ b, b ∈ MarkedFamilyCoherence.retained E heads →
    (∀ c, c ∈ MarkedFamilyCoherence.retained E heads → P c → MarkedFamilyLattice.le E heads c b = true) → MarkedFamilyLattice.le E heads sup b = true) ∧
  (∀ c, c ∈ MarkedFamilyCoherence.retained E heads → P c → MarkedFamilyLattice.le E heads inf c = true) ∧
  (∀ b, b ∈ MarkedFamilyCoherence.retained E heads →
    (∀ c, c ∈ MarkedFamilyCoherence.retained E heads → P c → MarkedFamilyLattice.le E heads b c = true) → MarkedFamilyLattice.le E heads b inf = true)

def FullFamilyLattice : Prop := OrderExact ∧ PartialOrder ∧ AggregateValid ∧ CombineSuccess ∧ Join ∧ Meet ∧ FiniteNonempty ∧ Complete
end LogicLineages.PersistentMarking.MarkedFamilyLatticeTargets
