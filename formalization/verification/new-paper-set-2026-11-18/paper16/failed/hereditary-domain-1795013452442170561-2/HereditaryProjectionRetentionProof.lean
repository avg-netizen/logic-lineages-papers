import LogicLineages.PersistentMarking.HereditaryProjectionLookupProof
namespace LogicLineages.PersistentMarking.HereditaryProjectionRetentionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem retained : HereditaryProjectionTargets.ProjectionRetained := by
  intro E σ Γ Θ c he hc
  obtain ⟨hfits,hmono,hnatural⟩ := (HereditaryConstructionProof.effective E σ Γ c).mp hc
  apply (HereditaryConstructionProof.effective E σ Θ _).mpr
  refine ⟨HereditaryProjectionLookupProof.fits E σ Γ Θ c he hfits,?_,?_⟩
  · unfold monotone at hmono ⊢
    apply List.all_eq_true.mpr
    intro Δ hΔ
    obtain ⟨hw,hΘΔ⟩ := (FiniteExtensionProof.enumeration E.types E.ports Θ Δ).mp hΔ
    have hΓΔ := DecisionPortsProof.extensionTrans Γ Θ Δ he hΘΔ
    have hΔold := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mpr ⟨hw,hΓΔ⟩
    have hm1 := (List.all_eq_true.mp hmono) Δ hΔold
    apply List.all_eq_true.mpr
    intro p hp
    have hm2 := (List.all_eq_true.mp hm1) p hp
    apply List.all_eq_true.mpr
    intro xs hx
    have hm3 := (List.all_eq_true.mp hm2) xs hx
    apply List.all_eq_true.mpr
    intro ys hy
    have hm4 := (List.all_eq_true.mp hm3) ys hy
    obtain ⟨a,ha,ham⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs c hw hΓΔ hc hx
    obtain ⟨b,hb,hbm⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p ys c hw hΓΔ hc hy
    have hpa := HereditaryProjectionLookupProof.output E σ Γ Θ Δ c p xs a hΘΔ ha
    have hpb := HereditaryProjectionLookupProof.output E σ Γ Θ Δ c p ys b hΘΔ hb
    by_cases hle : tupleLe σ (canonicalLower E σ) Δ p xs ys = true
    · simpa [hle,ha,hb,hpa,hpb] using hm4
    · simp only [if_neg hle]
  · unfold natural at hnatural ⊢
    apply List.all_eq_true.mpr
    intro Δ hΔ
    obtain ⟨hw,hΘΔ⟩ := (FiniteExtensionProof.enumeration E.types E.ports Θ Δ).mp hΔ
    have hΓΔ := DecisionPortsProof.extensionTrans Γ Θ Δ he hΘΔ
    have hΔold := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mpr ⟨hw,hΓΔ⟩
    have hn1 := (List.all_eq_true.mp hnatural) Δ hΔold
    apply List.all_eq_true.mpr
    intro Ξ hΞ
    obtain ⟨hwΞ,hΔΞ⟩ := (FiniteExtensionProof.enumeration E.types E.ports Δ Ξ).mp hΞ
    have hΘΞ := DecisionPortsProof.extensionTrans Θ Δ Ξ hΘΔ hΔΞ
    have hn2 := (List.all_eq_true.mp hn1) Ξ hΞ
    apply List.all_eq_true.mpr
    intro p hp
    have hn3 := (List.all_eq_true.mp hn2) p hp
    apply List.all_eq_true.mpr
    intro xs hx
    have hn4 := (List.all_eq_true.mp hn3) xs hx
    obtain ⟨a,ha,ham⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs c hw hΓΔ hc hx
    have hpa := HereditaryProjectionLookupProof.output E σ Γ Θ Δ c p xs a hΘΔ ha
    cases hr : tupleRestrict σ (canonicalLower E σ) Δ Ξ p xs with
    | none => simp [hr] at hn4
    | some ys =>
      cases hb : output E σ (canonicalLower E σ) Γ Ξ p ys c with
      | none => simp [hr,ha,hb] at hn4
      | some b =>
        have hpb := HereditaryProjectionLookupProof.output E σ Γ Θ Ξ c p ys b hΘΞ hb
        simpa [hr,ha,hb,hpa,hpb] using hn4

end LogicLineages.PersistentMarking.HereditaryProjectionRetentionProof
