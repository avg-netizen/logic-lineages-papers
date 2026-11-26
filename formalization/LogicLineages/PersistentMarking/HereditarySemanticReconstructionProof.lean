import LogicLineages.PersistentMarking.HereditaryEncodeCoordinateProof
import LogicLineages.PersistentMarking.HereditaryDecodedValiditySupport
namespace LogicLineages.PersistentMarking.HereditarySemanticReconstructionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryEncodeCoordinateProof

theorem reconstruct (E : Environment) (σ : Ty) (Γ : Context) (v : Value) (hvalid : Valid E σ Γ v) :
    ValueEq E σ Γ (HereditaryDomainSemantics.decode E σ Γ (encode E σ Γ v)) v := by
  intro Δ hw he
  have avail : (⟨Δ,.available⟩,2) ∈ layout E σ (canonicalLower E σ) Γ := by
    apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
      E.types E.names E.ports E.target Γ _ _).mpr
    exact ⟨Δ,hw,he,rfl,Or.inl ⟨rfl,rfl⟩⟩
  refine ⟨?_,?_,?_⟩
  · have hl := lookupEncoded E σ Γ v _ 2 avail
    change ((lookup (layout E σ (canonicalLower E σ) Γ) (encode E σ Γ v) ⟨Δ,.available⟩).getD 0 == 1) = _
    rw [hl]
    cases hv : v.available Δ <;> simp [coordinate,hv]
  · intro t ht
    have weak : (⟨Δ,.weak t⟩,2) ∈ layout E σ (canonicalLower E σ) Γ := by
      apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
        E.types E.names E.ports E.target Γ _ _).mpr
      exact ⟨Δ,hw,he,rfl,Or.inr (Or.inl ⟨t,ht,rfl,rfl⟩)⟩
    have strict : (⟨Δ,.strict t⟩,2) ∈ layout E σ (canonicalLower E σ) Γ := by
      apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
        E.types E.names E.ports E.target Γ _ _).mpr
      exact ⟨Δ,hw,he,rfl,Or.inr (Or.inr (Or.inl ⟨t,ht,rfl,rfl⟩))⟩
    constructor
    · have hl := lookupEncoded E σ Γ v _ 2 weak
      change ((lookup (layout E σ (canonicalLower E σ) Γ) (encode E σ Γ v) ⟨Δ,.weak t⟩).getD 0 == 1) = _
      rw [hl]
      cases hv : v.weak Δ t <;> simp [coordinate,hv]
    · have hl := lookupEncoded E σ Γ v _ 2 strict
      change ((lookup (layout E σ (canonicalLower E σ) Γ) (encode E σ Γ v) ⟨Δ,.strict t⟩).getD 0 == 1) = _
      rw [hl]
      cases hv : v.strict Δ t <;> simp [coordinate,hv]
  · intro ds τ hp vs hvs
    let p : Prefix σ := ⟨(ds,τ),hp⟩
    obtain ⟨is,his,hdecode,hvector⟩ := HereditaryDecodedValiditySupport.codeTuple E σ Δ p vs hvs
    have hm : (⟨Δ,.application ds τ is⟩,((descriptor E τ).carriers Δ).length) ∈ layout E σ (canonicalLower E σ) Γ := by
      apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
        E.types E.names E.ports E.target Γ _ _).mpr
      exact ⟨Δ,hw,he,rfl,Or.inr (Or.inr (Or.inr ⟨ds,τ,hp,is,
        (FiniteVectorProof.exactVector _ _).mp hvector,rfl,rfl⟩))⟩
    have hout := hvalid.1 Δ hw he ds τ hp vs hvs
    obtain ⟨i,hi⟩ := HereditaryLookupProof.indexExists _ (v.application Δ ds τ vs) hout
    have hget := HereditaryLookupProof.indexSound _ (v.application Δ ds τ vs) i hi
    have hvalues : HereditaryDomainSemantics.values E Δ ds is = some vs := by
      rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hdecode
      exact hdecode
    have hl := lookupEncoded E σ Γ v _ _ hm
    have hc : coordinate E v (⟨Δ,.application ds τ is⟩,((descriptor E τ).carriers Δ).length) = i := by
      simp [coordinate,hvalues,hi]
    rw [hc] at hl
    change indices E Δ ds vs = some is at his
    simp [HereditaryDomainSemantics.decode,his,hl,hget]

end LogicLineages.PersistentMarking.HereditarySemanticReconstructionProof
