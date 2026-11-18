import LogicLineages.PersistentMarking.TypeSupport
namespace LogicLineages.PersistentMarking.TypeSupportTargets
open Spine NameBridge StructuralContext TypeSupport

def RootSupport : Prop := ∀ q ρ, ρ ∈ subtypes q.type → ρ ∈ support q
def ShiftSupport : Prop := ∀ k d q, support (shift k d q) = support q
def ClosingSupport : Prop := ∀ name q, support (close name q) = support q
def EncodingSupport : Prop := ∀ env q, support (encode env q) = namedSupport q

def ExactSubstitution : Prop := ∀ S q τ θ,
  PaperTerm S q τ → Ordinary q → StructuralStabilityTargets.OrdinaryMap S θ →
  ∀ ρ, ρ ∈ support (freeSub θ 0 q) ↔ ρ ∈ support q ∨ ImageSupport θ q ρ

def SubstitutionConfinement : Prop := ∀ S s t τ θ,
  PaperTerm S s τ → PaperTerm S t τ → Ordinary s → Ordinary t →
  Included t s → (∀ name, freeOccurs name t = true → freeOccurs name s = true) →
  StructuralStabilityTargets.OrdinaryMap S θ → Included (freeSub θ 0 t) (freeSub θ 0 s)

def ContextConfinement : Prop := ∀ S C σ τ s t,
  ContextTyped S C σ τ → PaperTerm S s σ → PaperTerm S t σ → Ordinary s → Ordinary t →
  Included t s → Included (fill C t) (fill C s)

def FullConfinementStability : Prop := SubstitutionConfinement ∧ ContextConfinement

def NamedSubstitutionEncoding : Prop := ∀ S η q τ,
  NamedOrdinaryMap S η → NamedTyped q τ → NamedValid S q → StructuralCoverageTargets.NamedOrdinary q →
  encode [] (namedSubstitute η q) = freeSub (encodeMap η) 0 (encode [] q)

def NamedExactSubstitution : Prop := ∀ S η q τ,
  NamedOrdinaryMap S η → NamedTyped q τ → NamedValid S q → StructuralCoverageTargets.NamedOrdinary q →
  ∀ ρ, ρ ∈ namedSupport (namedSubstitute η q) ↔ ρ ∈ namedSupport q ∨
    ∃ σ x, freeOccurs (σ,x) (encode [] q) = true ∧ ρ ∈ namedSupport (η σ x)

def NamedContextConfinement : Prop := ∀ S C σ τ s t,
  StructuralCoverageTargets.NamedContextTyped S C σ τ →
  NamedTyped s σ → NamedValid S s → StructuralCoverageTargets.NamedOrdinary s →
  NamedTyped t σ → NamedValid S t → StructuralCoverageTargets.NamedOrdinary t →
  (∀ ρ, ρ ∈ namedSupport t → ρ ∈ namedSupport s) →
  ∀ ρ, ρ ∈ namedSupport (namedFill C t) → ρ ∈ namedSupport (namedFill C s)
end LogicLineages.PersistentMarking.TypeSupportTargets
