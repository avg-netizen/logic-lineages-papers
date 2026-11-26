import LogicLineages.PersistentMarking.HereditaryProjectionLookupProof
import LogicLineages.PersistentMarking.HereditaryDecodedValiditySupport
namespace LogicLineages.PersistentMarking.HereditaryProjectionSemanticsProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem lookupSame (E : Environment) (σ : Ty) (Γ Θ : Context) (c : Code) (key : Key) (bound : Nat)
    (hc : c ∈ (descriptor E σ).carriers Γ) (he : Extends Θ key.context)
    (hm : (key,bound) ∈ layout E σ (canonicalLower E σ) Γ) :
    lookup (layout E σ (canonicalLower E σ) Θ) (project E σ (canonicalLower E σ) Γ Θ c) key =
      lookup (layout E σ (canonicalLower E σ) Γ) c key := by
  have hf := ((HereditaryConstructionProof.effective E σ Γ c).mp hc).1
  obtain ⟨i,hi⟩ := HereditaryCoordinateProof.lookupExists _ c key bound hf hm
  rw [HereditaryProjectionLookupProof.lookup E σ Γ Θ c key i he hi,hi]

theorem semantics : HereditaryProjectionTargets.ProjectionSemantics := by
  intro E σ Γ Θ c he hc Δ hw hΘΔ
  have hΓΔ := DecisionPortsProof.extensionTrans Γ Θ Δ he hΘΔ
  have avail : (⟨Δ,.available⟩,2) ∈ layout E σ (canonicalLower E σ) Γ := by
    apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
      E.types E.names E.ports E.target Γ _ _).mpr
    exact ⟨Δ,hw,hΓΔ,rfl,Or.inl ⟨rfl,rfl⟩⟩
  refine ⟨?_,?_,?_⟩
  · have hl := lookupSame E σ Γ Θ c _ 2 hc hΘΔ avail
    simp only [HereditaryDomainSemantics.decode,hl]
  · intro t ht
    have weak : (⟨Δ,.weak t⟩,2) ∈ layout E σ (canonicalLower E σ) Γ := by
      apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
        E.types E.names E.ports E.target Γ _ _).mpr
      exact ⟨Δ,hw,hΓΔ,rfl,Or.inr (Or.inl ⟨t,ht,rfl,rfl⟩)⟩
    have strict : (⟨Δ,.strict t⟩,2) ∈ layout E σ (canonicalLower E σ) Γ := by
      apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
        E.types E.names E.ports E.target Γ _ _).mpr
      exact ⟨Δ,hw,hΓΔ,rfl,Or.inr (Or.inr (Or.inl ⟨t,ht,rfl,rfl⟩))⟩
    constructor
    · have hl := lookupSame E σ Γ Θ c _ 2 hc hΘΔ weak
      simp only [HereditaryDomainSemantics.decode,hl]
    · have hl := lookupSame E σ Γ Θ c _ 2 hc hΘΔ strict
      simp only [HereditaryDomainSemantics.decode,hl]
  · intro ds τ hp vs hvs
    let p : Prefix σ := ⟨(ds,τ),hp⟩
    obtain ⟨is,his,hd,hvector⟩ := HereditaryDecodedValiditySupport.codeTuple E σ Δ p vs hvs
    obtain ⟨a,ha,ham⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p is c hw hΓΔ hc hvector
    have hpa := HereditaryProjectionLookupProof.output E σ Γ Θ Δ c p is a hΘΔ ha
    have ho := HereditaryDecodedValiditySupport.decodedOutput E σ Γ Δ p c is vs a his ha
    have hn := HereditaryDecodedValiditySupport.decodedOutput E σ Θ Δ p
      (project E σ (canonicalLower E σ) Γ Θ c) is vs a his hpa
    exact hn.trans ho.symm

end LogicLineages.PersistentMarking.HereditaryProjectionSemanticsProof
