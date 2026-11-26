module
public import LogicLineages.CartierObserverCurrent.CanonicalExtensionTargets
public import LogicLineages.CartierObserverCurrent.NaturalityProof
public meta import LogicLineages.Audit

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.CanonicalExtension

private theorem presentation {K : Type u} {L : Type v} [Field K] [Field L]
    (σ : K →+* L) (f : RatFunc K) :
    Naturality.rationalMap σ f =
      algebraMap (Polynomial L) (RatFunc L) (f.num.map σ) /
      algebraMap (Polynomial L) (RatFunc L) (f.denom.map σ) := by
  conv_lhs => rw [← f.num_div_denom]
  rw [map_div₀, Naturality.extensionPolynomial, Naturality.extensionPolynomial]

private theorem cross {K : Type u} {L : Type v} [Field K] [Field L]
    (σ : K →+* L) (f : RatFunc K) :
    (Naturality.rationalMap σ f).num * f.denom.map σ =
      f.num.map σ * (Naturality.rationalMap σ f).denom := by
  apply (RatFunc.num_mul_eq_mul_denom_iff ?_).mpr (presentation σ f)
  exact Polynomial.map_ne_zero f.denom_ne_zero

theorem denominatorMap : Targets.DenominatorMap.{u,v} := by
  intro K L _ _ σ f
  let g := Naturality.rationalMap σ f
  have h := cross σ f
  have hcop := (RatFunc.isCoprime_num_denom f).map (Polynomial.mapRingHom σ)
  have hd₁ : g.denom ∣ f.denom.map σ := by
    apply (RatFunc.isCoprime_num_denom g).symm.dvd_of_dvd_mul_left
    rw [h]
    exact dvd_mul_left _ _
  have hd₂ : f.denom.map σ ∣ g.denom := by
    apply hcop.symm.dvd_of_dvd_mul_left
    change f.denom.map σ ∣ f.num.map σ * (Naturality.rationalMap σ f).denom
    rw [← h]
    exact dvd_mul_left _ _
  exact Polynomial.eq_of_monic_of_associated g.monic_denom (f.monic_denom.map σ)
    (associated_of_dvd_dvd hd₁ hd₂)

theorem numeratorMap : Targets.NumeratorMap.{u,v} := by
  intro K L _ _ σ f
  have h := cross σ f
  rw [denominatorMap K L σ f] at h
  exact mul_right_cancel₀ (Polynomial.map_ne_zero f.denom_ne_zero) h

theorem properMap : Targets.ProperMap.{u,v} := by
  intro K L _ _ σ f
  unfold MixedProper.proper
  rw [numeratorMap K L σ f, denominatorMap K L σ f,
    Polynomial.degree_map_eq_of_injective σ.injective,
    Polynomial.degree_map_eq_of_injective σ.injective]

#audit_namespace LogicLineages.CartierObserverCurrent.CanonicalExtension
end LogicLineages.CartierObserverCurrent.CanonicalExtension
