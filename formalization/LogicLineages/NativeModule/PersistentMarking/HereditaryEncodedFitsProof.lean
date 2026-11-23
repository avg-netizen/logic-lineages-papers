module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryEncodingTargets
public import LogicLineages.NativeModule.PersistentMarking.HereditaryEncodeCoordinateProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryEncodedFitsProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryEncodeCoordinateProof

theorem mappedFits (schema : List (Key × Nat)) (f : Key × Nat → Nat)
    (h : ∀ kb, kb ∈ schema → f kb < kb.2) : Fits (schema.map Prod.snd) (schema.map f) := by
  induction schema with
  | nil => trivial
  | cons kb ks ih =>
    exact ⟨h kb (List.mem_cons_self),ih (fun k hk => h k (List.mem_cons_of_mem _ hk))⟩

theorem coordinateBound (E : Environment) (σ : Ty) (Γ : Context) (v : Value)
    (hvalid : Valid E σ Γ v) (key : Key) (bound : Nat)
    (hm : (key,bound) ∈ layout E σ (canonicalLower E σ) Γ) : coordinate E v (key,bound) < bound := by
  obtain ⟨Δ,hw,he,hctx,hkind⟩ := (FiniteSchemaExactProof.exactSchema σ
    (lowerCodes σ (canonicalLower E σ)) E.types E.names E.ports E.target Γ key bound).mp hm
  cases key with
  | mk context kind =>
    change context = Δ at hctx
    subst context
    rcases hkind with ⟨hk,hb⟩|⟨t,ht,hk,hb⟩|⟨t,ht,hk,hb⟩|⟨ds,τ,hp,is,hfit,hk,hb⟩
    · cases hk; subst bound
      change (if v.available Δ then 1 else 0) < 2
      split <;> decide
    · cases hk; subst bound
      change (if v.weak Δ t then 1 else 0) < 2
      split <;> decide
    · cases hk; subst bound
      change (if v.strict Δ t then 1 else 0) < 2
      split <;> decide
    · cases hk; subst bound
      let p : Prefix σ := ⟨(ds,τ),hp⟩
      have hvector : is ∈ vectors (tupleBounds σ (canonicalLower E σ) Δ p) :=
        (FiniteVectorProof.exactVector _ _).mpr hfit
      obtain ⟨vs,hvs⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mp hvector
      rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hvs
      change HereditaryDomainSemantics.values E Δ ds is = some vs at hvs
      have ht := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ ds is vs hvs).1
      have hout := hvalid.1 Δ hw he ds τ hp vs ht
      obtain ⟨i,hi⟩ := HereditaryLookupProof.indexExists _ (v.application Δ ds τ vs) hout
      have hget := HereditaryLookupProof.indexSound _ (v.application Δ ds τ vs) i hi
      have hb := (List.getElem?_eq_some_iff.mp hget).1
      simpa [coordinate,hvs,hi,outputBound,lowerCodes,canonicalLower] using hb

theorem fits : HereditaryEncodingTargets.EncodedFits := by
  intro E σ Γ v hvalid
  rw [encodeMap]
  exact mappedFits _ _ (fun kb hkb => coordinateBound E σ Γ v hvalid kb.1 kb.2 hkb)

end LogicLineages.PersistentMarking.HereditaryEncodedFitsProof
