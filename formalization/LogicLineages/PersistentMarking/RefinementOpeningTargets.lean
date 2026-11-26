import LogicLineages.PersistentMarking.RefinementRenamingTargets
namespace LogicLineages.PersistentMarking.RefinementOpeningTargets
open Spine NameBridge RefinementMeasure

/-- Synchronize two genuinely fresh choices of opening name without changing
any recursive witness count. The body itself is not modified or identified
silently modulo alpha. -/
def Synchronize : Prop := ∀ S σ x y q s,
  freeOccurs (σ,x) q = false → freeOccurs (σ,x) s = false →
  freeOccurs (σ,y) q = false → freeOccurs (σ,y) s = false →
  ∀ h : RefinementTree S (openBody σ x q) (openBody σ x s),
    ∃ h' : RefinementTree S (openBody σ y q) (openBody σ y s), treeSize h' = treeSize h

end LogicLineages.PersistentMarking.RefinementOpeningTargets
