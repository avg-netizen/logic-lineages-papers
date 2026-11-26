import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticOccurrencePartitionTargets
open NumberedWindowArithmeticDirectMultisetTargets

def forgetOrigin : Sum Nat Nat → Nat := Sum.elim id id

/-- Transport the source component tags along the supplied kept/removed
permutation. Both projections recover the exact supplied lists, including
every repetition of an address shared by the two components. -/
def KeptRemovedByOrigin : Prop :=
  ∀ left right kept removed : List Nat,
    (left ++ right).Perm (kept ++ removed) →
    ∃ keptTagged removedTagged : List (Sum Nat Nat),
      (left.map Sum.inl ++ right.map Sum.inr).Perm (keptTagged ++ removedTagged) ∧
      keptTagged.map forgetOrigin = kept ∧ removedTagged.map forgetOrigin = removed

/-- A strict replacement out of a union splits into two component
replacements, allowing either component to stay unchanged up to permutation
and requiring at least one strict decrease. -/
def DirectAddressUnionSplit : Prop :=
  ∀ S K left right target,
    AddressDirect S K (left ++ right) target →
    ∃ leftTarget rightTarget, target.Perm (leftTarget ++ rightTarget) ∧
      ((AddressDirect S K left leftTarget ∧
          (right.Perm rightTarget ∨ AddressDirect S K right rightTarget)) ∨
        (left.Perm leftTarget ∧ AddressDirect S K right rightTarget))

end LogicLineages.PersistentMarking.NumberedWindowArithmeticOccurrencePartitionTargets
