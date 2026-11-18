import LogicLineages.PersistentMarking.ElementaryBridgeTargets
namespace LogicLineages.PersistentMarking.ElementaryBridgeProof
open Spine NameBridge

theorem markEncoding (env : List Name) (q : Term) :
    mark (encode env q) = (Term.mark q).map (encode env) := by
  cases q with
  | var σ x => cases hl : nameLookup env (σ,x) <;> simp [encode,hl,mark,Term.mark]
  | lam σ x body =>
    simp only [encode,mark,Term.mark,markEncoding ((σ,x)::env) body,Option.map_map]
    rfl
  | head f base => rfl
  | marked f τ base extras => rfl
termination_by sizeOf q
end LogicLineages.PersistentMarking.ElementaryBridgeProof
