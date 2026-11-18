import LogicLineages.PersistentMarking.HereditaryLookupProof
namespace LogicLineages.PersistentMarking.HereditaryCoordinateProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem lookupExists (schema : List (Key × Nat)) (code : Code) (key : Key) (bound : Nat)
    (hf : Fits (schema.map Prod.snd) code) (hm : (key,bound) ∈ schema) :
    ∃ v, lookup schema code key = some v := by
  induction schema generalizing code with
  | nil => cases hm
  | cons kb ks ih =>
    cases code with
    | nil => cases hf
    | cons v vs =>
      by_cases he : keyEq kb.1 key = true
      · exact ⟨v,by simp [lookup,he]⟩
      · have hk : (key,bound) ∈ ks := (List.mem_cons.mp hm).elim
          (fun h => False.elim (he ((HereditaryLookupProof.keyExact _ _).mpr (congrArg Prod.fst h.symm)))) id
        obtain ⟨w,hw⟩ := ih vs hf.2 hk
        exact ⟨w,by simp only [lookup,if_neg he]; exact hw⟩

end LogicLineages.PersistentMarking.HereditaryCoordinateProof
