module

public import LogicLineages.ComputabilityKnowledge.GorbowContextTransport
public import LogicLineages.ComputabilityKnowledge.GorbowTermShiftCode

@[expose] public section

/-! Structural compatibility for actual capture-avoiding substitution. Only
occurring source indices require a compatible replacement; unused entries do
not impose out-of-context transport obligations. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowContextSubstitution
open GorbowSyntax GorbowFreeSupport

def Compatible {n m k l : Nat} (support : Finset Nat)
    (σ : Fin n → Term k) (τ : Fin m → Term l) : Prop :=
  ∀ (i : Fin n) (j : Fin m), i.val=j.val → i.val∈support →
    GorbowContextTransport.term l (σ i)=some (τ j)
end LogicLineages.ComputabilityKnowledge.GorbowContextSubstitution
