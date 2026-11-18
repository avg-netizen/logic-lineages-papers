import LogicLineages.PersistentMarking.MarkedBaseTuples
namespace LogicLineages.PersistentMarking.MarkedBaseTupleTargets
open Spine NameBridge DecisionPorts DecisionInventory DecisionSourceUniverse FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedBaseTuples

def TupleEnumeration : Prop := ∀ E Γ ds vs, vs ∈ tuples E Γ ds ↔ TupleValues E Γ ds vs

def TupleDistinct : Prop := ∀ E Γ ds, (tuples E Γ ds).Pairwise (· ≠ ·)

def TupleOrderExact : Prop := ∀ E Γ ds xs ys, TupleValues E Γ ds xs → TupleValues E Γ ds ys →
  (tupleLe E Γ ds xs ys = true ↔ ValuesLE E Γ ds xs ys)

def TupleOrder : Prop := ∀ E Γ ds, WellFormed E.types E.ports Γ →
  (∀ xs, TupleValues E Γ ds xs → tupleLe E Γ ds xs xs = true) ∧
  (∀ xs ys zs, TupleValues E Γ ds xs → TupleValues E Γ ds ys → TupleValues E Γ ds zs →
    tupleLe E Γ ds xs ys = true → tupleLe E Γ ds ys zs = true → tupleLe E Γ ds xs zs = true) ∧
  (∀ xs ys, TupleValues E Γ ds xs → TupleValues E Γ ds ys →
    tupleLe E Γ ds xs ys = true → tupleLe E Γ ds ys xs = true → xs=ys)

def TupleRestriction : Prop := ∀ E Γ Θ ds xs,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ →
  TupleValues E Γ ds xs → TupleValues E Θ ds (restrictTuple E Γ Θ ds xs)

def TupleRestrictionMonotone : Prop := ∀ E Γ Θ ds xs ys,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ →
  TupleValues E Γ ds xs → TupleValues E Γ ds ys → tupleLe E Γ ds xs ys = true →
  tupleLe E Θ ds (restrictTuple E Γ Θ ds xs) (restrictTuple E Γ Θ ds ys) = true

def TupleRestrictionAlgebra : Prop := ∀ E ds,
  (∀ Γ xs, WellFormed E.types E.ports Γ → TupleValues E Γ ds xs → restrictTuple E Γ Γ ds xs = xs) ∧
  (∀ Γ Δ Θ xs, WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ →
    WellFormed E.types E.ports Θ → Extends Γ Δ → Extends Δ Θ → TupleValues E Γ ds xs →
    restrictTuple E Δ Θ ds (restrictTuple E Γ Δ ds xs) = restrictTuple E Γ Θ ds xs)

def HeadDeclaration : Prop := ∀ q f, f ∈ heads q → ∀ ρ, ρ ∈ declaration f → ρ ∈ auxiliarySupport q

def SourceHeadCoverage : Prop := ∀ s t σ τ,
  Typed EmptyContext s σ → Typed EmptyContext t τ → Ordinary s → Ordinary t →
  ∀ f, f ∈ (inventory s t).sourceHeads →
    f.result ∈ (inventory s t).types ∧ (∀ ρ, ρ ∈ f.arguments → ρ ∈ (inventory s t).types)
end LogicLineages.PersistentMarking.MarkedBaseTupleTargets
