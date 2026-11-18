import LogicLineages.PersistentMarking.ProtectedSpineEnvironment

namespace LogicLineages.PersistentMarking.ProtectedSpineEnvironmentTargets
open Spine DecisionPorts HereditaryDomainCode ProtectedSpineEnvironment

def FreeValid (E : Environment) (Γ : Context) (free : FreeValues) : Prop :=
  ∀ a, a ∈ free → a.2 ∈ (descriptor E a.1.1).carriers Γ

def BoundValid (E : Environment) (Γ : Context) (bound : BoundValues) : Prop :=
  ∀ a, a ∈ bound → a.2 ∈ (descriptor E a.1).carriers Γ

def Weakening : Prop := ∀ E Γ Δ free bound,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ → Extends Γ Δ →
  FreeValid E Γ free → BoundValid E Γ bound →
  FreeValid E Δ (weakenFree E Γ Δ free) ∧ BoundValid E Δ (weakenBound E Γ Δ bound)

def EnvironmentComposition : Prop := ∀ E Γ Δ Θ free bound,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ → WellFormed E.types E.ports Θ →
  Extends Γ Δ → Extends Δ Θ → FreeValid E Γ free → BoundValid E Γ bound →
  weakenFree E Δ Θ (weakenFree E Γ Δ free) = weakenFree E Γ Θ free ∧
  weakenBound E Δ Θ (weakenBound E Γ Δ bound) = weakenBound E Γ Θ bound

def CodeLookup : Prop := ∀ E Γ free bound σ x i,
  WellFormed E.types E.ports Γ → FreeValid E Γ free → BoundValid E Γ bound →
  freeCode E Γ free σ x ∈ (descriptor E σ).carriers Γ ∧
  boundCode E Γ bound σ i ∈ (descriptor E σ).carriers Γ

def LookupWeakening : Prop := ∀ E Γ Δ free bound σ x i,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ → Extends Γ Δ →
  FreeValid E Γ free → BoundValid E Γ bound →
  (descriptor E σ).restrict Γ Δ (freeCode E Γ free σ x) = freeCode E Δ (weakenFree E Γ Δ free) σ x ∧
  (descriptor E σ).restrict Γ Δ (boundCode E Γ bound σ i) = boundCode E Δ (weakenBound E Γ Δ bound) σ i

end LogicLineages.PersistentMarking.ProtectedSpineEnvironmentTargets
