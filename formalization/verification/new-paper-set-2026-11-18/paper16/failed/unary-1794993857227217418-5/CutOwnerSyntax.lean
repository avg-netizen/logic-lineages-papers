import LogicLineages.PersistentMarking.ExtendedComparison
namespace LogicLineages.PersistentMarking.CutOwnerSyntax
open Spine

/-- Proof-local classification of the three actual marked-target creating
root clauses, retaining all original base/extra premises. Not a replacement
comparison relation and not closed under any auxiliary rule. -/
def Root (S : Signature) (f : Head) (sb se : Args) (g : Head) (tb te : Args) : Prop :=
  (Equivalent S f g ∧ _root_.Nonempty (ExtendedMatchingTree S sb tb) ∧
    _root_.Nonempty (ExtendedOrderedTree S se te)) ∨
  (Precedes S f g ∧ _root_.Nonempty (ExtendedWholeTree S f sb se tb) ∧
    _root_.Nonempty (ExtendedWholeTree S f sb se te)) ∨
  (Equivalent S f g ∧ _root_.Nonempty (ExtendedMultisetTree S sb tb) ∧
    _root_.Nonempty (ExtendedWholeTree S f sb se tb) ∧
    _root_.Nonempty (ExtendedWholeTree S f sb se te))
end LogicLineages.PersistentMarking.CutOwnerSyntax
