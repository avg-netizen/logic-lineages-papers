import LogicLineages.PersistentMarking.HereditaryDomainTargets
namespace LogicLineages.PersistentMarking.HereditaryNaturalityBridgeTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def TupleLeExact : Prop := ∀ E σ Δ (p : Prefix σ) xs ys vs ws,
  tupleDecode σ (canonicalLower E σ) Δ p xs = some vs →
  tupleDecode σ (canonicalLower E σ) Δ p ys = some ws →
  (tupleLe σ (canonicalLower E σ) Δ p xs ys = true ↔ ValuesLE E Δ p.val.1 vs ws)

def TupleRestrictionExact : Prop := ∀ E σ Δ Θ (p : Prefix σ) xs vs,
  tupleDecode σ (canonicalLower E σ) Δ p xs = some vs →
  tupleRestrict σ (canonicalLower E σ) Δ Θ p xs =
    indices E Θ p.val.1 (restrictValues E Δ Θ p.val.1 vs)

def DecodedValid : Prop := ∀ E σ Γ c,
  WellFormed E.types E.ports Γ → c ∈ (descriptor E σ).carriers Γ → Valid E σ Γ (decode E σ Γ c)

end LogicLineages.PersistentMarking.HereditaryNaturalityBridgeTargets
