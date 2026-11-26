import LogicLineages.PersistentMarking.ExtendedComparison
namespace LogicLineages.PersistentMarking.TargetExtrasTargets
open Spine

/-- Delete an arbitrary literal suffix of the marked target's extras. -/
def SuffixRemoval : Prop := ∀ S s f τ base extras suffix,
  ExtendedWeak S s (.marked f τ base (extras.append suffix)) →
  ExtendedWeak S s (.marked f τ base extras)

/-- Permute all target occurrences, retaining multiplicity. -/
def TargetPermutation : Prop := ∀ S s f τ base extras reordered,
  ExtendedWeak S s (.marked f τ base extras) → Permutation extras reordered →
  ExtendedWeak S s (.marked f τ base reordered)

/-- Append finite prefix copies of the original target, each at its own type. -/
def CopyAddition : Prop := ∀ S s f τ base extras copies,
  ExtendedWeak S s (.marked f τ base extras) → PrefixCopies f base extras copies →
  ExtendedWeak S s (.marked f τ base (extras.append copies))

def FullTargetExtras : Prop := SuffixRemoval ∧ TargetPermutation ∧ CopyAddition
end LogicLineages.PersistentMarking.TargetExtrasTargets
