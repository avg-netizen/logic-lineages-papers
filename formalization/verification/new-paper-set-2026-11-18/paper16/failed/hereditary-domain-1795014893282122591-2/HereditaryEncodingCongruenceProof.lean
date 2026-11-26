import LogicLineages.PersistentMarking.HereditaryOrderTargets
import LogicLineages.PersistentMarking.HereditaryCodeReconstructionProof
namespace LogicLineages.PersistentMarking.HereditaryEncodingCongruenceProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryEncodeCoordinateProof

theorem congruence : HereditaryOrderTargets.EncodingCongruence := by
  intro E σ Γ a b hab
  rw [encodeMap,encodeMap]
  apply List.map_congr_left
  intro kb hm
  obtain ⟨key,bound⟩ := kb
  obtain ⟨Δ,hw,he,hctx,hkind⟩ := (FiniteSchemaExactProof.exactSchema σ
    (lowerCodes σ (canonicalLower E σ)) E.types E.names E.ports E.target Γ key bound).mp hm
  have hab := hab Δ hw he
  cases key with
  | mk context kind =>
    change context = Δ at hctx
    subst context
    rcases hkind with ⟨hk,hb⟩|⟨t,ht,hk,hb⟩|⟨t,ht,hk,hb⟩|⟨ds,τ,hp,is,hfit,hk,hb⟩
    · cases hk
      simp only [coordinate,hab.1]
    · cases hk
      simp only [coordinate,(hab.2.1 t ht).1]
    · cases hk
      simp only [coordinate,(hab.2.1 t ht).2]
    · cases hk
      let p : Prefix σ := ⟨(ds,τ),hp⟩
      have hvector : is ∈ vectors (tupleBounds σ (canonicalLower E σ) Δ p) :=
        (FiniteVectorProof.exactVector _ _).mpr hfit
      obtain ⟨vs,hvs⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mp hvector
      rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hvs
      change HereditaryDomainSemantics.values E Δ ds is = some vs at hvs
      have ht := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ ds is vs hvs).1
      simp [coordinate,hvs,hab.2.2 ds τ hp vs ht]

theorem injective : HereditaryOrderTargets.CodeInjective := by
  intro E σ Γ a b ha hb hab
  have h := congruence E σ Γ _ _ hab
  rw [HereditaryCodeReconstructionProof.reconstruct E σ Γ a ha,
    HereditaryCodeReconstructionProof.reconstruct E σ Γ b hb] at h
  exact h
end LogicLineages.PersistentMarking.HereditaryEncodingCongruenceProof
