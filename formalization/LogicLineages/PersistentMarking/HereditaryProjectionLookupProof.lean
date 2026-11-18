import LogicLineages.PersistentMarking.HereditaryProjectionTargets
import LogicLineages.PersistentMarking.HereditaryEncodedFitsProof
namespace LogicLineages.PersistentMarking.HereditaryProjectionLookupProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem lookupMember (schema : List (Key × Nat)) (code : Code) (key : Key) (i : Nat)
    (h : lookup schema code key = some i) : ∃ bound, (key,bound) ∈ schema := by
  induction schema generalizing code with
  | nil => cases h
  | cons kb ks ih =>
    cases code with
    | nil => cases h
    | cons v vs =>
      by_cases he : keyEq kb.1 key = true
      · have hk := (HereditaryLookupProof.keyExact _ _).mp he
        refine ⟨kb.2,List.mem_cons.mpr (Or.inl ?_)⟩
        cases kb
        simp_all
      · simp only [lookup,if_neg he] at h
        obtain ⟨b,hb⟩ := ih vs h
        exact ⟨b,List.mem_cons_of_mem _ hb⟩

theorem descendantMember (E : Environment) (σ : Ty) (Γ Θ : Context) (key : Key) (bound : Nat)
    (hm : (key,bound) ∈ layout E σ (canonicalLower E σ) Γ)
    (he : Extends Θ key.context) : (key,bound) ∈ layout E σ (canonicalLower E σ) Θ := by
  obtain ⟨Δ,hw,hΓ,hlocal⟩ := (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ key bound).mp hm
  apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Θ key bound).mpr
  rw [hlocal.1] at he
  exact ⟨Δ,hw,he,hlocal⟩

theorem lookup : HereditaryProjectionTargets.LookupProjection := by
  intro E σ Γ Θ c key i he hl
  obtain ⟨bound,hm⟩ := lookupMember _ c key i hl
  have hmΘ := descendantMember E σ Γ Θ key bound hm he
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hmΘ
  have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Θ
  apply HereditaryLookupProof.lookupAt _ _ j key bound i hd hj
  unfold project
  simp only [List.getElem?_map,hj,Option.map_some,hl,Option.getD_some]

theorem fits : HereditaryProjectionTargets.ProjectionFits := by
  intro E σ Γ Θ c he hf
  unfold project
  apply HereditaryEncodedFitsProof.mappedFits
  intro kb hkb
  have hm := FiniteSchemaExactProof.restrictionKeys σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ Θ he kb.1 kb.2 hkb
  have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ))
    E.types E.names E.ports E.target Γ
  obtain ⟨v,hv,hb⟩ := HereditaryCoordinateBoundsProof.lookupCoordinate _ c kb.1 kb.2 hd hf hm
  change HereditaryDomainCode.lookup (layout E σ (canonicalLower E σ) Γ) c kb.1 = some v at hv
  rw [hv]
  exact hb

theorem output : HereditaryProjectionTargets.OutputProjection := by
  intro E σ Γ Θ Δ c p tuple v he ho
  unfold HereditaryDomainCode.output at ho ⊢
  cases hi : HereditaryDomainCode.lookup (layout E σ (canonicalLower E σ) Γ) c
      ⟨Δ,.application p.val.1 p.val.2 tuple⟩ with
  | none => simp [hi] at ho
  | some i =>
    have hnew := lookup E σ Γ Θ c ⟨Δ,.application p.val.1 p.val.2 tuple⟩ i he hi
    rw [hnew]
    simpa [hi] using ho

end LogicLineages.PersistentMarking.HereditaryProjectionLookupProof
