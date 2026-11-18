import LogicLineages.PersistentMarking.HereditaryCoordinateProof
namespace LogicLineages.PersistentMarking.HereditaryCoordinateBoundsProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem lookupCoordinate (schema : List (Key × Nat)) (code : Code) (key : Key) (bound : Nat)
    (hd : (schema.map Prod.fst).Pairwise (· ≠ ·))
    (hf : Fits (schema.map Prod.snd) code) (hm : (key,bound) ∈ schema) :
    ∃ v, lookup schema code key = some v ∧ v < bound := by
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨hlen,hbounds⟩ := (FiniteVectorProof.coordinates _ _).mp hf
  have hs : i < schema.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlength : schema.length = code.length := by simpa only [List.length_map] using hlen
  have hc : i < code.length := by omega
  let v := code[i]'hc
  have hv : code[i]? = some v := List.getElem?_eq_some_iff.mpr ⟨hc,rfl⟩
  have hb : (schema.map Prod.snd)[i]? = some bound := by
    simp only [List.getElem?_map,hi,Option.map_some]
  exact ⟨v,HereditaryLookupProof.lookupAt schema code i key bound v hd hi hv,hbounds i bound v hb hv⟩

end LogicLineages.PersistentMarking.HereditaryCoordinateBoundsProof
