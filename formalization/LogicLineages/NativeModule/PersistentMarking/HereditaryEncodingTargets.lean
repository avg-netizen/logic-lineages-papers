module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryDomainTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryEncodingTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def SemanticRoundtrip : Prop := ∀ E σ Γ v, Valid E σ Γ v →
  ValueEq E σ Γ (HereditaryDomainSemantics.decode E σ Γ (encode E σ Γ v)) v

def EncodedFits : Prop := ∀ E σ Γ v, Valid E σ Γ v →
  Fits ((layout E σ (canonicalLower E σ) Γ).map Prod.snd) (encode E σ Γ v)

/- An explicit proper-type induction contract on the actual global descriptor.
This is not a premise of the final hereditary theorem. -/
def LowerRestriction (E : Environment) (σ : Ty) : Prop :=
  ∀ ρ, typeSize ρ < typeSize σ → ∀ Δ Θ,
  WellFormed E.types E.ports Δ → WellFormed E.types E.ports Θ → Extends Δ Θ →
  ∀ c, c ∈ (descriptor E ρ).carriers Δ →
    (descriptor E ρ).restrict Δ Θ c ∈ (descriptor E ρ).carriers Θ

def EncodedRetained : Prop := ∀ E σ Γ v,
  WellFormed E.types E.ports Γ → LowerRestriction E σ → Valid E σ Γ v →
    encode E σ Γ v ∈ (descriptor E σ).carriers Γ

end LogicLineages.PersistentMarking.HereditaryEncodingTargets
