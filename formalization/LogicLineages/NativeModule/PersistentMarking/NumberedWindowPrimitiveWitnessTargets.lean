module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimitiveWitnessBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessTargets
open NumberedWindowSyntax NumberedWindowRules NumberedWindowPrimitiveWitnessBits

def ExactLiteralMarkBit : Prop :=
  ∀ Q R, markBit Q R = true ↔ MarkDecrease Q R

def ExactLiteralPermutationBit : Prop :=
  ∀ xs ys, permBit xs ys = true ↔ List.Perm xs ys

/-- This is the original open matrix at exactly the supplied partition.
The occurrence lists need not be distinct; deletion has empty added. -/
def SuppliedReplacementMatrix (source target : NArgs) (w : ReplacementWitness) : Prop :=
  source.toList.Perm (w.kept ++ w.removed) ∧
  target.toList.Perm (w.kept ++ w.added) ∧
  w.removed ≠ [] ∧ ∀ a ∈ w.added, ∃ b ∈ w.removed, MarkDecrease b a

def ExactSuppliedReplacementBit : Prop :=
  ∀ source target w, replacementBit source target w = true ↔
    SuppliedReplacementMatrix source target w

def ExactCertifiedPrimitiveReplacement : Prop :=
  ∀ source target, (∃ w, replacementBit source target w = true) ↔
    PrimitiveReplacement source target

end LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessTargets
