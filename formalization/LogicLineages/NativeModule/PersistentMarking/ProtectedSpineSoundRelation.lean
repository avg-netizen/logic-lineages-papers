module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyTargets
public import LogicLineages.NativeModule.PersistentMarking.FinitePrefixProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundRelation
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics PortNormalization ProtectedSpineAdequacyTargets

/-- Every actual observation and whole tuple at every extension of the root.
The concrete side of a tuple is the original closed, typed argument spine. -/
def Related (F : Inputs S) (σ : Ty) (Γ : Context) (c : Code) (result : Option Expr) : Prop :=
  c ∈ (descriptor (domain F) σ).carriers Γ ∧
  match result with
  | none => c = StructuralActions.bottom (domain F) σ Γ
  | some q =>
    ∀ Δ, WellFormed F.data.types F.data.ports Δ → Extends Γ Δ →
      (∀ t, t ∈ observations F.data.names F.data.ports Δ F.target σ →
        ((decode (domain F) σ Γ c).weak Δ t = true → Weak S q t) ∧
        ((decode (domain F) σ Γ c).strict Δ t = true → Strict S q t)) ∧
      (∀ ds τ, (ds,τ) ∈ fullPrefixes σ → ∀ xs args,
        TupleValues (domain F) Δ ds xs →
        CallTyped EmptyContext σ args τ → Sources F Δ args →
        (∀ i ρ x a, ds[i]? = some ρ → xs[i]? = some x → At args i a → Related F ρ Δ x (some a)) →
        Related F τ Δ ((decode (domain F) σ Γ c).application Δ ds τ xs) (apply q args))
termination_by typeSize σ
decreasing_by
  · exact (FinitePrefixProof.proper _ _ _ ‹_ ∈ _›).2 _ (List.mem_of_getElem? ‹_ = some _›)
  · exact (FinitePrefixProof.proper _ _ _ ‹_ ∈ _›).1

def Bottom : Prop := ∀ S (F : Inputs S) σ Γ r, WellFormed F.data.types F.data.ports Γ →
  Related F σ Γ (StructuralActions.bottom (domain F) σ Γ) r

def Downward : Prop := ∀ S (F : Inputs S) σ Γ a b r,
  WellFormed F.data.types F.data.ports Γ →
  a ∈ (descriptor (domain F) σ).carriers Γ → (descriptor (domain F) σ).le Γ a b = true →
  Related F σ Γ b r → Related F σ Γ a r

def Restriction : Prop := ∀ S (F : Inputs S) σ Γ Δ c r,
  WellFormed F.data.types F.data.ports Γ → WellFormed F.data.types F.data.ports Δ → Extends Γ Δ →
  Related F σ Γ c r → Related F σ Δ ((descriptor (domain F) σ).restrict Γ Δ c) r

def SoundObservation : Prop := ∀ S (F : Inputs S) Γ q t σ,
  WellFormed F.data.types F.data.ports Γ → Source F Γ q → Observed F Γ t →
  PaperTerm S q σ → PaperTerm S t σ →
  ((FixedValue S F Γ q).weak Γ t = true → Weak S q t) ∧
  ((FixedValue S F Γ q).strict Γ t = true → Strict S q t)

end LogicLineages.PersistentMarking.ProtectedSpineSoundRelation
