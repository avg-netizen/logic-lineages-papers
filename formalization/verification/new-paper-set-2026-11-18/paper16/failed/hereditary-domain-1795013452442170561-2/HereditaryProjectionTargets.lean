import LogicLineages.PersistentMarking.HereditaryDomainTargets
namespace LogicLineages.PersistentMarking.HereditaryProjectionTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def ProjectionFits : Prop := ∀ E σ Γ Θ c, Extends Γ Θ →
  Fits ((layout E σ (canonicalLower E σ) Γ).map Prod.snd) c →
  Fits ((layout E σ (canonicalLower E σ) Θ).map Prod.snd)
    (project E σ (canonicalLower E σ) Γ Θ c)

/- Actual successful lookup itself witnesses original schema membership;
future-context inclusion supplies the descendant schema coordinate. -/
def LookupProjection : Prop := ∀ E σ Γ Θ c (key : Key) i,
  Extends Θ key.context → lookup (layout E σ (canonicalLower E σ) Γ) c key = some i →
  lookup (layout E σ (canonicalLower E σ) Θ)
    (project E σ (canonicalLower E σ) Γ Θ c) key = some i

def OutputProjection : Prop := ∀ E σ Γ Θ Δ c (p : Prefix σ) tuple v,
  Extends Θ Δ → output E σ (canonicalLower E σ) Γ Δ p tuple c = some v →
  output E σ (canonicalLower E σ) Θ Δ p tuple
    (project E σ (canonicalLower E σ) Γ Θ c) = some v

def ProjectionRetained : Prop := ∀ E σ Γ Θ c, Extends Γ Θ →
  c ∈ (descriptor E σ).carriers Γ →
  project E σ (canonicalLower E σ) Γ Θ c ∈ (descriptor E σ).carriers Θ

def ProjectionSemantics : Prop := ∀ E σ Γ Θ c, Extends Γ Θ →
  c ∈ (descriptor E σ).carriers Γ →
  ValueEq E σ Θ
    (HereditaryDomainSemantics.decode E σ Θ (project E σ (canonicalLower E σ) Γ Θ c))
    (HereditaryDomainSemantics.decode E σ Γ c)

end LogicLineages.PersistentMarking.HereditaryProjectionTargets
