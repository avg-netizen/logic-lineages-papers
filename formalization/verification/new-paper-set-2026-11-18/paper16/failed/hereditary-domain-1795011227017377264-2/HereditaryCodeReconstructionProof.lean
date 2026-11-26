import LogicLineages.PersistentMarking.HereditaryEncodeCoordinateProof
import LogicLineages.PersistentMarking.HereditaryVectorRebuildProof
namespace LogicLineages.PersistentMarking.HereditaryCodeReconstructionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryEncodeCoordinateProof

theorem coordinateRebuild (E : Environment) (σ : Ty) (Γ : Context) (c : Code) (key : Key) (bound v : Nat)
    (hm : (key,bound) ∈ layout E σ (canonicalLower E σ) Γ)
    (hl : lookup (layout E σ (canonicalLower E σ) Γ) c key = some v)
    (hv : v < bound) : coordinate E (decode E σ Γ c) (key,bound) = v := by
  obtain ⟨Δ,hw,he,hctx,hkind⟩ := (FiniteSchemaExactProof.exactSchema σ
    (lowerCodes σ (canonicalLower E σ)) E.types E.names E.ports E.target Γ key bound).mp hm
  cases key with
  | mk context kind =>
    simp only [Key.context] at hctx
    subst context
    rcases hkind with ⟨hk,hb⟩|⟨t,ht,hk,hb⟩|⟨t,ht,hk,hb⟩|⟨ds,τ,hp,is,hfit,hk,hb⟩
    · cases hk; subst bound
      simpa only [coordinate,decode,hl,Option.getD_some] using bitRoundtrip v hv
    · cases hk; subst bound
      simpa only [coordinate,decode,hl,Option.getD_some] using bitRoundtrip v hv
    · cases hk; subst bound
      simpa only [coordinate,decode,hl,Option.getD_some] using bitRoundtrip v hv
    · cases hk; subst bound
      let p : Prefix σ := ⟨(ds,τ),hp⟩
      have hvector : is ∈ vectors (tupleBounds σ (canonicalLower E σ) Δ p) :=
        (FiniteVectorProof.exactVector _ _).mpr hfit
      obtain ⟨vs,hvs⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mp hvector
      rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hvs
      have hind := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ ds is vs hvs).2
      change v < ((descriptor E τ).carriers Δ).length at hv
      let value := ((descriptor E τ).carriers Δ)[v]'hv
      have hget : ((descriptor E τ).carriers Δ)[v]? = some value :=
        List.getElem?_eq_some_iff.mpr ⟨hv,rfl⟩
      have hindex := HereditaryLookupProof.indexAt _ value v (HereditaryConstructionProof.distinct E τ Δ) hget
      have hdecoded : (decode E σ Γ c).application Δ ds τ vs = value := by
        simp only [decode,hind,Option.bind_some,hl,hget,Option.getD_some]
      simp only [coordinate,hvs,Option.bind_some,hdecoded,hindex,Option.getD_some]

theorem reconstruct (E : Environment) (σ : Ty) (Γ : Context) (c : Code)
    (hc : c ∈ (descriptor E σ).carriers Γ) : encode E σ Γ (decode E σ Γ c) = c := by
  rw [encodeMap]
  have hf := ((HereditaryConstructionProof.effective E σ Γ c).mp hc).1
  obtain ⟨hlen,hbounds⟩ := (FiniteVectorProof.coordinates _ _).mp hf
  have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ
  apply HereditaryVectorRebuildProof.rebuild _ c _
  · simpa only [List.length_map] using hlen
  · intro i kb v hk hv
    have hb : ((layout E σ (canonicalLower E σ) Γ).map Prod.snd)[i]? = some kb.2 := by
      simp only [List.getElem?_map,hk,Option.map_some]
    exact coordinateRebuild E σ Γ c kb.1 kb.2 v (List.mem_of_getElem? hk)
      (HereditaryLookupProof.lookupAt _ c i kb.1 kb.2 v hd hk hv) (hbounds i kb.2 v hb hv)

end LogicLineages.PersistentMarking.HereditaryCodeReconstructionProof
