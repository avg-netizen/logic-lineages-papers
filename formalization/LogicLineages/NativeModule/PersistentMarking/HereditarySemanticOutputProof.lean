module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryOutputProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditarySemanticOutputProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem decodeOutput (E : Environment) (σ : Ty) (Γ Δ : Context) (c : Code) (ds : List Ty) (τ : Ty)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hc : c ∈ (descriptor E σ).carriers Γ) (hp : (ds,τ) ∈ fullPrefixes σ)
    (vs : List Code) (ht : TupleValues E Δ ds vs) :
    (decode E σ Γ c).application Δ ds τ vs ∈ (descriptor E τ).carriers Δ := by
  obtain ⟨is,his⟩ := HereditaryTupleProof.indicesExist E Δ ds vs ht
  have hv := (HereditaryTupleProof.valuesAfterIndices E Δ ds vs is his).2
  let p : Prefix σ := ⟨(ds,τ),hp⟩
  have hd : tupleDecode σ (canonicalLower E σ) Δ p is = some vs := by
    rw [HereditaryTupleAdapterProof.tupleDecodeCanonical]
    exact hv
  have hf := (HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mpr ⟨vs,hd⟩
  obtain ⟨v,hvout,hvmem⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p is c hw he hc hf
  have heq : (decode E σ Γ c).application Δ ds τ vs = v := by
    change ((do
      let tuple ← indices E Δ ds vs
      let i ← lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.application ds τ tuple⟩
      ((descriptor E τ).carriers Δ)[i]?) : Option Code).getD [] = v
    rw [his]
    change (output E σ (canonicalLower E σ) Γ Δ p is c).getD [] = v
    rw [hvout]
    rfl
  rw [heq]
  exact hvmem

end LogicLineages.PersistentMarking.HereditarySemanticOutputProof
