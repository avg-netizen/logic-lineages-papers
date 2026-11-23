module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorOperator

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorOperatorTargets
open Spine DecisionInventory FiniteDomainSchema HereditaryDomainCode MarkedConstructorOperator
open HereditaryDomainSemantics (ValueEq)

def Endomap (S : Signature) (E : Environment) (heads : List Head) : Prop :=
  ∀ M, M ∈ MarkedFamilyCoherence.retained E heads →
    MarkedFamilyCoding.encode E heads (nextFamily S E heads M) = some (step S E heads M) ∧
    step S E heads M ∈ MarkedFamilyCoherence.retained E heads ∧
    ∀ p, MarkedFamilyParameters.Valid E heads p →
      ValueEq E p.2.1 p.2.2.1
        (HereditaryDomainSemantics.decode E p.2.1 p.2.2.1
          (MarkedFamilyCoding.decode E heads (step S E heads M) p))
        (MarkedConstructorValue.build S E heads M p)

def Monotone (S : Signature) (E : Environment) (heads : List Head) : Prop :=
  ∀ M N, M ∈ MarkedFamilyCoherence.retained E heads → N ∈ MarkedFamilyCoherence.retained E heads →
    MarkedFamilyLattice.le E heads M N = true →
    MarkedFamilyLattice.le E heads (step S E heads M) (step S E heads N) = true

def Stabilizes (S : Signature) (E : Environment) (heads : List Head) : Prop :=
  let bound := (MarkedFamilyCoherence.retained E heads).length
  let L := leastFixedPoint S E heads
  (∀ n, iterate S E heads n ∈ MarkedFamilyCoherence.retained E heads) ∧
  (∀ m n, m ≤ n → MarkedFamilyLattice.le E heads (iterate S E heads m) (iterate S E heads n) = true) ∧
  (∀ n, bound ≤ n → iterate S E heads n = L) ∧
  step S E heads L = L ∧
  ∀ M, M ∈ MarkedFamilyCoherence.retained E heads → step S E heads M = M →
    MarkedFamilyLattice.le E heads L M = true

/-- Paper16 lem:operator, at the literal ordinary input inventory. -/
def Operator : Prop :=
  ∀ S s t σ τ, PaperTerm S s σ → PaperTerm S t τ → Ordinary s → Ordinary t →
    let E := environment s t
    let heads := (inventory s t).sourceHeads
    Endomap S E heads ∧ Monotone S E heads ∧ Stabilizes S E heads

end LogicLineages.PersistentMarking.MarkedConstructorOperatorTargets
