module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryCoordinateBoundsProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryPrefixCodingProof
public import LogicLineages.NativeModule.PersistentMarking.FiniteSchemaDistinctProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryOutputProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem outputExists (E : Environment) (σ : Ty) (Γ Δ : Context) (p : Prefix σ) (tuple : List Nat) (c : Code)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hc : c ∈ (descriptor E σ).carriers Γ)
    (ht : tuple ∈ vectors (tupleBounds σ (canonicalLower E σ) Δ p)) :
    ∃ v, output E σ (canonicalLower E σ) Γ Δ p tuple c = some v ∧
      v ∈ (descriptor E p.val.2).carriers Δ := by
  have hf := ((HereditaryConstructionProof.effective E σ Γ c).mp hc).1
  have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ
  have hm : (⟨Δ,.application p.val.1 p.val.2 tuple⟩,((descriptor E p.val.2).carriers Δ).length) ∈
      layout E σ (canonicalLower E σ) Γ := by
    apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
      E.types E.names E.ports E.target Γ _ _).mpr
    refine ⟨Δ,hw,he,rfl,Or.inr (Or.inr (Or.inr ?_))⟩
    exact ⟨p.val.1,p.val.2,p.property,tuple,(FiniteVectorProof.exactVector _ _).mp ht,rfl,rfl⟩
  obtain ⟨i,hi,hbound⟩ := HereditaryCoordinateBoundsProof.lookupCoordinate _ c _ _ hd hf hm
  let v := ((descriptor E p.val.2).carriers Δ)[i]'hbound
  have hv : ((descriptor E p.val.2).carriers Δ)[i]? = some v :=
    List.getElem?_eq_some_iff.mpr ⟨hbound,rfl⟩
  refine ⟨v,?_,List.mem_of_getElem? hv⟩
  change lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,.application p.val.1 p.val.2 tuple⟩ = some i at hi
  unfold output
  rw [hi]
  exact hv

end LogicLineages.PersistentMarking.HereditaryOutputProof
