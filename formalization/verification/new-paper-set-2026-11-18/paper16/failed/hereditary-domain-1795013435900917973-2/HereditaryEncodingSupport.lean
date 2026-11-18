import LogicLineages.PersistentMarking.HereditaryEncodedFitsProof
namespace LogicLineages.PersistentMarking.HereditaryEncodingSupport
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryEncodeCoordinateProof

theorem restrictedTuple (E : Environment) (σ : Ty) (Δ Θ : Context) (ds : List Ty) (vs : List Code)
    (hsmall : ∀ ρ, ρ ∈ ds → typeSize ρ < typeSize σ)
    (hlower : HereditaryEncodingTargets.LowerRestriction E σ)
    (hΔ : WellFormed E.types E.ports Δ) (hΘ : WellFormed E.types E.ports Θ) (he : Extends Δ Θ)
    (ht : TupleValues E Δ ds vs) : TupleValues E Θ ds (restrictValues E Δ Θ ds vs) := by
  induction ds generalizing vs with
  | nil =>
    cases vs with
    | nil => exact HereditaryTupleProof.tupleNil E Θ
    | cons v vs => cases ht.1
  | cons ρ ds ih =>
    cases vs with
    | nil => cases ht.1
    | cons v vs =>
      have hparts := (HereditaryTupleProof.tupleCons E Δ ρ ds v vs).mp ht
      change TupleValues E Θ (ρ::ds) ((descriptor E ρ).restrict Δ Θ v :: restrictValues E Δ Θ ds vs)
      apply (HereditaryTupleProof.tupleCons E Θ ρ ds _ _).mpr
      exact ⟨hlower ρ (hsmall ρ List.mem_cons_self) Δ Θ hΔ hΘ he v hparts.1,
        ih vs (fun τ hτ => hsmall τ (List.mem_cons_of_mem _ hτ)) hparts.2⟩

theorem encodedOutput (E : Environment) (σ : Ty) (Γ Δ : Context) (v : Value) (p : Prefix σ)
    (is : List Nat) (vs : List Code) (hvalid : Valid E σ Γ v)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hd : tupleDecode σ (canonicalLower E σ) Δ p is = some vs) :
    output E σ (canonicalLower E σ) Γ Δ p is (encode E σ Γ v) =
      some (v.application Δ p.val.1 p.val.2 vs) := by
  have hvalues := hd
  rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hvalues
  have ht := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 is vs hvalues).1
  have hvector := (HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mpr ⟨vs,hd⟩
  have hm : (⟨Δ,.application p.val.1 p.val.2 is⟩,((descriptor E p.val.2).carriers Δ).length) ∈
      layout E σ (canonicalLower E σ) Γ := by
    apply (FiniteSchemaExactProof.exactSchema σ (lowerCodes σ (canonicalLower E σ))
      E.types E.names E.ports E.target Γ _ _).mpr
    exact ⟨Δ,hw,he,rfl,Or.inr (Or.inr (Or.inr ⟨p.val.1,p.val.2,p.property,is,
      (FiniteVectorProof.exactVector _ _).mp hvector,rfl,rfl⟩))⟩
  have hout := hvalid.1 Δ hw he p.val.1 p.val.2 p.property vs ht
  obtain ⟨i,hi⟩ := HereditaryLookupProof.indexExists _ (v.application Δ p.val.1 p.val.2 vs) hout
  have hget := HereditaryLookupProof.indexSound _ (v.application Δ p.val.1 p.val.2 vs) i hi
  have hl := lookupEncoded E σ Γ v _ _ hm
  have hcoord : coordinate E v (⟨Δ,.application p.val.1 p.val.2 is⟩,((descriptor E p.val.2).carriers Δ).length) = i := by
    simp [coordinate,hvalues,hi]
  rw [hcoord] at hl
  unfold output
  rw [hl]
  exact hget

end LogicLineages.PersistentMarking.HereditaryEncodingSupport
