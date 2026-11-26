module

public import LogicLineages.NativeModule.PersistentMarking.RefinementMeasure
public import LogicLineages.NativeModule.PersistentMarking.RefinementSyntaxTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementRenamingTargets
open Spine

abbrev NameRenaming := Ty → Nat → Nat

def injectiveNames (π : NameRenaming) : Prop := ∀ σ a b, π σ a = π σ b → a = b

def rename (π : NameRenaming) (q : Expr) : Expr := freeSub (fun σ x => .free σ (π σ x)) 0 q

def renameArgs (π : NameRenaming) (qs : Args) : Args := freeSubArgs (fun σ x => .free σ (π σ x)) 0 qs

/-- A genuine finite renamed witness, preserving its actual constructor count.
This is only the preliminary injective case, not the final arbitrary renaming law. -/
def SizePreservingRenaming : Prop := ∀ S π, injectiveNames π → ∀ q s (h : RefinementTree S q s),
  ∃ h' : RefinementTree S (rename π q) (rename π s),
    RefinementMeasure.treeSize h' = RefinementMeasure.treeSize h

end LogicLineages.PersistentMarking.RefinementRenamingTargets
