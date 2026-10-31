module
public import LogicLineages.ModelsAlgebra.Forests.RankedParseDefinitions
/-! Literal recursive deletion algorithm from repaired paper03's
parse-pruning proof. Selection is a Boolean predicate on leaf occurrences.
No graph evaluation, choice, or proof oracle is used by this computation. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm
open RankedParse

def prune : (t : Term) → (Leaf t → Bool) → Option Term
  | .atom, B => if B () then some .atom else none
  | .node o l r, B =>
    match prune l (fun x => B (.inl x)), prune r (fun y => B (.inr y)) with
    | none, none => none
    | some s, none => some s
    | none, some u => some u
    | some s, some u => some (.node o s u)

end LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm
