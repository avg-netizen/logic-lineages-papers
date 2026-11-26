module

public import LogicLineages.NativeModule.PersistentMarking.StructuralActions

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralActionTargets
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def FullActionSound : Prop := ∀ E σ Γ c ds τ xs,
  WellFormed E.types E.ports Γ → c ∈ (descriptor E σ).carriers Γ →
  (ds,τ) ∈ fullPrefixes σ → TupleValues E Γ ds xs →
  StructuralActions.fullAction E σ Γ c ds τ xs ∈ (descriptor E τ).carriers Γ

def FullActionMonotone : Prop := ∀ E σ Γ c d ds τ xs ys,
  WellFormed E.types E.ports Γ → c ∈ (descriptor E σ).carriers Γ → d ∈ (descriptor E σ).carriers Γ →
  (descriptor E σ).le Γ c d = true → (ds,τ) ∈ fullPrefixes σ →
  TupleValues E Γ ds xs → TupleValues E Γ ds ys → ValuesLE E Γ ds xs ys →
  (descriptor E τ).le Γ (StructuralActions.fullAction E σ Γ c ds τ xs)
    (StructuralActions.fullAction E σ Γ d ds τ ys) = true

def FullActionNatural : Prop := ∀ E σ Γ Δ c ds τ xs,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ → Extends Γ Δ →
  c ∈ (descriptor E σ).carriers Γ → (ds,τ) ∈ fullPrefixes σ → TupleValues E Γ ds xs →
  (descriptor E τ).restrict Γ Δ (StructuralActions.fullAction E σ Γ c ds τ xs) =
    StructuralActions.fullAction E σ Δ ((descriptor E σ).restrict Γ Δ c) ds τ
      (HereditaryDomainSemantics.restrictValues E Γ Δ ds xs)

def WholeBottom : Prop := ∀ E σ Γ, WellFormed E.types E.ports Γ →
  StructuralActions.bottom E σ Γ ∈ (descriptor E σ).carriers Γ ∧
  (∀ Δ, WellFormed E.types E.ports Δ → Extends Γ Δ →
    (HereditaryDomainSemantics.decode E σ Γ (StructuralActions.bottom E σ Γ)).available Δ = false ∧
    (∀ t, t ∈ observations E.names E.ports Δ E.target σ →
      (HereditaryDomainSemantics.decode E σ Γ (StructuralActions.bottom E σ Γ)).weak Δ t = false ∧
      (HereditaryDomainSemantics.decode E σ Γ (StructuralActions.bottom E σ Γ)).strict Δ t = false) ∧
    (∀ ds τ, (ds,τ) ∈ fullPrefixes σ → ∀ xs, TupleValues E Δ ds xs →
      (HereditaryDomainSemantics.decode E σ Γ (StructuralActions.bottom E σ Γ)).application Δ ds τ xs =
        StructuralActions.bottom E τ Δ))

def MarkedActionSound : Prop := ∀ E heads c p,
  c ∈ MarkedFamilyCoherence.retained E heads → MarkedFamilyParameters.Valid E heads p →
  ∃ v, StructuralActions.markedAction E heads c p = some v ∧
    v ∈ (descriptor E p.2.1).carriers p.2.2.1

def MarkedActionLaws : Prop := ∀ E heads c, c ∈ MarkedFamilyCoherence.retained E heads →
  (∀ p q a b, MarkedFamilyParameters.Valid E heads p → MarkedFamilyParameters.Valid E heads q →
    MarkedFamilyCoherence.InputLE E p q → StructuralActions.markedAction E heads c p = some a →
    StructuralActions.markedAction E heads c q = some b → (descriptor E p.2.1).le p.2.2.1 a b = true) ∧
  (∀ p Δ a b, MarkedFamilyParameters.Valid E heads p → WellFormed E.types E.ports Δ → Extends p.2.2.1 Δ →
    StructuralActions.markedAction E heads c p = some a →
    StructuralActions.markedAction E heads c (MarkedFamilyCoherence.weakenParameter E p Δ) = some b →
    (descriptor E p.2.1).restrict p.2.2.1 Δ a = b)

def ExtraInsertionValid : Prop := ∀ E Γ es xs,
  WellFormed E.types E.ports Γ → MarkedExtras.Extra E Γ es →
  (∀ x, x ∈ xs → x ∈ MarkedExtras.«universe» E Γ) →
  MarkedExtras.Extra E Γ (StructuralActions.insertExtras E Γ es xs)

def ExtraInsertionNatural : Prop := ∀ E Γ Δ es xs,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ → Extends Γ Δ →
  MarkedExtras.Extra E Γ es → (∀ x, x ∈ xs → x ∈ MarkedExtras.«universe» E Γ) →
  MarkedExtras.weaken E Γ Δ (StructuralActions.insertExtras E Γ es xs) =
    StructuralActions.insertExtras E Δ (MarkedExtras.weaken E Γ Δ es)
      (xs.map (MarkedExtras.restricted E Γ Δ))
end LogicLineages.PersistentMarking.StructuralActionTargets
