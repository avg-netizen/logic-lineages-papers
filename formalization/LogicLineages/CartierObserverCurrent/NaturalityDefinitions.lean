module
public import LogicLineages.CartierObserverCurrent.MixedWordDefinitions

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.Naturality

/-- Actual extension of a field coefficient embedding to the rational fraction field. -/
noncomputable def rationalMap {K : Type u} {L : Type v} [Field K] [Field L]
    (σ : K →+* L) : RatFunc K →+* RatFunc L :=
  IsFractionRing.lift (A := Polynomial K) (K := RatFunc K)
    (g := (algebraMap (Polynomial L) (RatFunc L)).comp (Polynomial.mapRingHom σ))
    ((RatFunc.algebraMap_injective L).comp (Polynomial.map_injective _ σ.injective))
end LogicLineages.CartierObserverCurrent.Naturality
