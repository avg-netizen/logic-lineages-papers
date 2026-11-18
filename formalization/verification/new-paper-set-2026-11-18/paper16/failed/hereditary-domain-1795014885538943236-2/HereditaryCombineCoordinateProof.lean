import LogicLineages.PersistentMarking.HereditaryCombineBitProof
import LogicLineages.PersistentMarking.HereditaryCombineOutputProof
import LogicLineages.PersistentMarking.HereditaryOrderBitProof
import LogicLineages.PersistentMarking.HereditaryEncodeCoordinateProof
namespace LogicLineages.PersistentMarking.HereditaryCombineCoordinateProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets HereditaryEncodeCoordinateProof

theorem bitCoordinate (E : Environment) (σ : Ty) (Γ Δ : Context) (meet : Bool) (cs : List Code)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hc : ∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ) (k : Kind)
    (hk : k ∈ HereditaryOrderBitProof.bits E σ Δ) :
    coordinate E (aggregate E meet (cs.map (HereditaryDomainSemantics.decode E σ Γ))) (⟨Δ,k⟩,2) =
      bitCombine meet (cs.map (fun c => (lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,k⟩).getD 0)) := by
  let f := fun c => HereditaryOrderBitProof.bit (HereditaryDomainSemantics.decode E σ Γ c) Δ k
  have hm : cs.map (fun c => (lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,k⟩).getD 0) =
      (cs.map f).map HereditaryCombineBitProof.number := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c hcm
    have hmember := HereditaryOrderBitProof.membership E σ Γ Δ hw he k hk
    have hd := FiniteSchemaDistinctProof.full σ (lowerCodes σ (canonicalLower E σ)) E.types E.names E.ports E.target Γ
    obtain ⟨i,hi,hib⟩ := HereditaryCoordinateBoundsProof.lookupCoordinate _ c _ 2 hd
      ((HereditaryConstructionProof.effective E σ Γ c).mp (hc c hcm)).1 hmember
    change lookup (layout E σ (canonicalLower E σ) Γ) c ⟨Δ,k⟩ = some i at hi
    have hb := HereditaryOrderBitProof.bitLookup E σ Γ Δ c k i hk hi
    change _ = HereditaryCombineBitProof.number (HereditaryOrderBitProof.bit (HereditaryDomainSemantics.decode E σ Γ c) Δ k)
    rw [hi,hb]
    exact (HereditaryEncodeCoordinateProof.bitRoundtrip i hib).symm
  rw [hm,HereditaryCombineBitProof.combine]
  simp only [HereditaryOrderBitProof.bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hk
  rcases hk with (hk|hk)|hk
  · cases hk
    cases meet <;> simp [coordinate,aggregate,HereditaryCombineBitProof.number,f,HereditaryOrderBitProof.bit]
  · obtain ⟨t,ht,rfl⟩ := hk
    cases meet <;> simp [coordinate,aggregate,HereditaryCombineBitProof.number,f,HereditaryOrderBitProof.bit]
  · obtain ⟨t,ht,rfl⟩ := hk
    cases meet <;> simp [coordinate,aggregate,HereditaryCombineBitProof.number,f,HereditaryOrderBitProof.bit]

theorem application (E : Environment) (σ : Ty) (Γ Δ : Context) (p : Prefix σ)
    (meet : Bool) (cs : List Code) (is : List Nat)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hc : ∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ)
    (his : is ∈ vectors (tupleBounds σ (canonicalLower E σ) Δ p)) :
    coordinate E (aggregate E meet (cs.map (HereditaryDomainSemantics.decode E σ Γ)))
      (⟨Δ,.application p.val.1 p.val.2 is⟩,outputBound σ (lowerCodes σ (canonicalLower E σ)) Δ p.val.1 p.val.2 p.property) =
    (indexOf ((descriptor E p.val.2).carriers Δ)
      (if meet then (descriptor E p.val.2).meet Δ (cs.filterMap (output E σ (canonicalLower E σ) Γ Δ p is))
       else (descriptor E p.val.2).join Δ (cs.filterMap (output E σ (canonicalLower E σ) Γ Δ p is)))).getD 0 := by
  obtain ⟨vs,hvs⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p is).mp his
  have hm := HereditaryCombineOutputProof.outputs E σ Γ Δ p is vs cs hw he hc hvs
  rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hvs
  simp only [coordinate,hvs,Option.bind_some,aggregate,List.map_map,hm]
  rfl

end LogicLineages.PersistentMarking.HereditaryCombineCoordinateProof
