import LogicLineages.PersistentMarking.HereditaryProjectionLookupProof
import LogicLineages.PersistentMarking.HereditaryVectorRebuildProof
namespace LogicLineages.PersistentMarking.HereditaryRestrictionAlgebraProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem projectIdentity (E : Environment) (σ : Ty) (Γ : Context) (c : Code)
    (hc : c ∈ (descriptor E σ).carriers Γ) : project E σ (canonicalLower E σ) Γ Γ c = c := by
  have hf := ((HereditaryConstructionProof.effective E σ Γ c).mp hc).1
  have hlen := ((FiniteVectorProof.coordinates _ _).mp hf).1
  have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ
  unfold project
  apply HereditaryVectorRebuildProof.rebuild
  · simpa only [List.length_map] using hlen
  · intro i kb v hk hv
    have hl := HereditaryLookupProof.lookupAt _ c i kb.1 kb.2 v hd hk hv
    change lookup (layout E σ (canonicalLower E σ) Γ) c kb.1 = some v at hl
    rw [hl]
    rfl

theorem projectComposition (E : Environment) (σ : Ty) (Γ Δ Θ : Context) (c : Code)
    (he : Extends Γ Δ) (hf : Extends Δ Θ) (hc : c ∈ (descriptor E σ).carriers Γ) :
    project E σ (canonicalLower E σ) Δ Θ (project E σ (canonicalLower E σ) Γ Δ c) =
      project E σ (canonicalLower E σ) Γ Θ c := by
  have hfits := ((HereditaryConstructionProof.effective E σ Γ c).mp hc).1
  change (layout E σ (canonicalLower E σ) Θ).map
    (fun kb => (lookup (layout E σ (canonicalLower E σ) Δ) (project E σ (canonicalLower E σ) Γ Δ c) kb.1).getD 0) =
    (layout E σ (canonicalLower E σ) Θ).map
    (fun kb => (lookup (layout E σ (canonicalLower E σ) Γ) c kb.1).getD 0)
  apply List.map_congr_left
  intro kb hkb
  have hmΓ := FiniteSchemaExactProof.restrictionKeys σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ Θ (DecisionPortsProof.extensionTrans Γ Δ Θ he hf) kb.1 kb.2 hkb
  obtain ⟨Ξ,hw,hΘΞ,hlocal⟩ := (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Θ kb.1 kb.2).mp hkb
  have hΔctx : Extends Δ kb.1.context := by
    rw [hlocal.1]
    exact DecisionPortsProof.extensionTrans Δ Θ Ξ hf hΘΞ
  obtain ⟨i,hi⟩ := HereditaryCoordinateProof.lookupExists _ c kb.1 kb.2 hfits hmΓ
  change lookup (layout E σ (canonicalLower E σ) Γ) c kb.1 = some i at hi
  have hnew := HereditaryProjectionLookupProof.lookup E σ Γ Δ c kb.1 i hΔctx hi
  rw [hnew,hi]

theorem restrictEq (E : Environment) (σ : Ty) :
    (descriptor E σ).restrict = project E σ (canonicalLower E σ) := by
  rw [HereditaryConstructionProof.equation E σ]
  rfl

theorem algebra : HereditaryDomainTargets.RestrictionIdentityComposition := by
  intro E σ
  constructor
  · intro Γ c hw hc
    rw [restrictEq]
    exact projectIdentity E σ Γ c hc
  · intro Γ Δ Θ c hΓ hΔ hΘ he hf hc
    rw [restrictEq]
    exact projectComposition E σ Γ Δ Θ c he hf hc

end LogicLineages.PersistentMarking.HereditaryRestrictionAlgebraProof
