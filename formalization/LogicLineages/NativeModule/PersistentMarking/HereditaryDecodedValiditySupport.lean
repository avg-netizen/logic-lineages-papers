module

public import LogicLineages.NativeModule.PersistentMarking.HereditarySemanticOutputProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryTupleOrderProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryTupleRestrictionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryDecodedValiditySupport
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem codeTuple (E : Environment) (σ : Ty) (Δ : Context) (p : Prefix σ) (vs : List Code)
    (h : TupleValues E Δ p.val.1 vs) : ∃ is,
    indices E Δ p.val.1 vs = some is ∧ tupleDecode σ (canonicalLower E σ) Δ p is = some vs ∧
    is ∈ vectors (tupleBounds σ (canonicalLower E σ) Δ p) := by
  obtain ⟨is,his⟩ := HereditaryTupleProof.indicesExist E Δ p.val.1 vs h
  have hv := (HereditaryTupleProof.valuesAfterIndices E Δ p.val.1 vs is his).2
  have hd : tupleDecode σ (canonicalLower E σ) Δ p is = some vs := by
    rw [HereditaryTupleAdapterProof.tupleDecodeCanonical]; exact hv
  exact ⟨is,his,hd,(HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mpr ⟨vs,hd⟩⟩

theorem decodedOutput (E : Environment) (σ : Ty) (Γ Δ : Context) (p : Prefix σ)
    (c : Code) (is : List Nat) (vs : List Code) (out : Code)
    (hi : indices E Δ p.val.1 vs = some is)
    (ho : output E σ (canonicalLower E σ) Γ Δ p is c = some out) :
    (HereditaryDomainSemantics.decode E σ Γ c).application Δ p.val.1 p.val.2 vs = out := by
  change ((do
    let tuple ← indices E Δ p.val.1 vs
    let i ← lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.application p.val.1 p.val.2 tuple⟩
    ((descriptor E p.val.2).carriers Δ)[i]?) : Option Code).getD [] = out
  rw [hi]
  change (output E σ (canonicalLower E σ) Γ Δ p is c).getD [] = out
  rw [ho]
  rfl

end LogicLineages.PersistentMarking.HereditaryDecodedValiditySupport
