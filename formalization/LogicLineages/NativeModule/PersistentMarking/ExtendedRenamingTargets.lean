module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedMeasure
public import LogicLineages.NativeModule.PersistentMarking.RefinementRenamingTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedRenamingTargets
open Spine RefinementRenamingTargets

def renameJudgment (π : NameRenaming) : ExtendedJudgment → ExtendedJudgment
  | .weak q t => .weak (rename π q) (rename π t)
  | .strict q t => .strict (rename π q) (rename π t)
  | .matching xs ys => .matching (renameArgs π xs) (renameArgs π ys)
  | .multiset xs ys => .multiset (renameArgs π xs) (renameArgs π ys)
  | .coverage xs ys => .coverage (renameArgs π xs) (renameArgs π ys)
  | .whole f base extras qs => .whole f (renameArgs π base) (renameArgs π extras) (renameArgs π qs)
  | .ordered xs ys => .ordered (renameArgs π xs) (renameArgs π ys)

/-- All seven judgments and all 25 constructors, without a covariance/cut
premise. The actual renamed finite tree has exactly the original node count. -/
def SizePreservingRenaming : Prop := ∀ S π, injectiveNames π → ∀ j (h : ExtendedTree S j),
  ∃ h' : ExtendedTree S (renameJudgment π j), ExtendedMeasure.treeSize h' = ExtendedMeasure.treeSize h
end LogicLineages.PersistentMarking.ExtendedRenamingTargets
