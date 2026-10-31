module
public import LogicLineages.ModelsAlgebra.Forests.RankedParseDefinitions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC
open RankedParse

/-- Exactly the same-operation association and permutation moves used when
flattening a binary parse. It does not identify different operations. -/
inductive AssociationEquivalent : Term → Term → Prop where
  | refl (t) : AssociationEquivalent t t
  | symm {s t} : AssociationEquivalent s t → AssociationEquivalent t s
  | trans {r s t} : AssociationEquivalent r s → AssociationEquivalent s t → AssociationEquivalent r t
  | congr {s s' t t'} (o) : AssociationEquivalent s s' → AssociationEquivalent t t' →
      AssociationEquivalent (.node o s t) (.node o s' t')
  | swap (o s t) : AssociationEquivalent (.node o s t) (.node o t s)
  | assoc (o r s t) : AssociationEquivalent (.node o (.node o r s) t) (.node o r (.node o s t))

def chosenLeaf : (t : Term) → Leaf t
  | .atom => ()
  | .node _ s _ => .inl (chosenLeaf s)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC
