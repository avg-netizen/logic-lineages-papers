module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedRenamingTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedOpeningTargets
open Spine NameBridge

def AbsSynchronize : Prop := ∀ S σ x y s t,
  freeOccurs (σ,x) s = false → freeOccurs (σ,x) t = false →
  freeOccurs (σ,y) s = false → freeOccurs (σ,y) t = false →
  ∀ h : ExtendedWeakTree S (openBody σ x s) (openBody σ x t),
    ∃ h' : ExtendedWeakTree S (openBody σ y s) (openBody σ y t),
      ExtendedMeasure.treeSize h' = ExtendedMeasure.treeSize h

def FAbsSynchronize : Prop := ∀ S f σ τ base extras body x y,
  freeOccurs (σ,x) (.marked f (.arrow σ τ) base extras) = false →
  freeOccurs (σ,x) body = false →
  freeOccurs (σ,y) (.marked f (.arrow σ τ) base extras) = false →
  freeOccurs (σ,y) body = false →
  ∀ h : ExtendedWeakTree S (.marked f τ base (extras.append (.cons (.free σ x) .nil))) (openBody σ x body),
    ∃ h' : ExtendedWeakTree S (.marked f τ base (extras.append (.cons (.free σ y) .nil))) (openBody σ y body),
      ExtendedMeasure.treeSize h' = ExtendedMeasure.treeSize h
end LogicLineages.PersistentMarking.ExtendedOpeningTargets
