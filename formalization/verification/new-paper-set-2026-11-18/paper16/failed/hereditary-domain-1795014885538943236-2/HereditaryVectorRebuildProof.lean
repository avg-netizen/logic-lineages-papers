import LogicLineages.PersistentMarking.HereditaryCoordinateBoundsProof
namespace LogicLineages.PersistentMarking.HereditaryVectorRebuildProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

/- A coordinate-by-coordinate equality criterion; the function is fixed
throughout the induction, so original whole-schema lookups are not replaced
by tail lookups. -/
theorem rebuild (schema : List (Key × Nat)) (code : Code) (f : Key × Nat → Nat)
    (hlen : schema.length = code.length)
    (h : ∀ (i : Nat) (kb : Key × Nat) (v : Nat),
      schema[i]? = some kb → code[i]? = some v → f kb = v) : schema.map f = code := by
  induction schema generalizing code with
  | nil =>
    cases code with
    | nil => rfl
    | cons v vs => cases hlen
  | cons kb ks ih =>
    cases code with
    | nil => cases hlen
    | cons v vs =>
      have hhead := h 0 kb v rfl rfl
      have htail := ih vs (Nat.succ.inj hlen)
        (fun i k w hk hw => h (i+1) k w hk hw)
      simp only [List.map_cons,hhead,htail]

end LogicLineages.PersistentMarking.HereditaryVectorRebuildProof
