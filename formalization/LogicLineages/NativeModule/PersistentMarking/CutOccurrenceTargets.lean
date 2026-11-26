module

public import LogicLineages.NativeModule.PersistentMarking.CutEdgeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.CutOccurrenceTargets
open Spine ExtendedMeasure

def WeakWeak : Prop := ∀ S n, CutEdgeTargets.Below S n → ∀ xs ys zs,
  _root_.Nonempty (ExtendedMatchingTree S xs ys) →
  ∀ right : ExtendedMatchingTree S ys zs, treeSize right < n → OrdinaryArgs zs →
  _root_.Nonempty (ExtendedMatchingTree S xs zs)

def WeakStrict : Prop := ∀ S n, CutEdgeTargets.Below S n → ∀ xs ys zs,
  _root_.Nonempty (ExtendedMatchingTree S xs ys) →
  ∀ right : ExtendedMultisetTree S ys zs, treeSize right < n → OrdinaryArgs zs →
  _root_.Nonempty (ExtendedMultisetTree S xs zs)

def StrictWeak : Prop := ∀ S n, CutEdgeTargets.Below S n → ∀ xs ys zs,
  _root_.Nonempty (ExtendedMultisetTree S xs ys) →
  ∀ right : ExtendedMatchingTree S ys zs, treeSize right < n → OrdinaryArgs zs →
  _root_.Nonempty (ExtendedMultisetTree S xs zs)

def StrictStrict : Prop := ∀ S n, CutEdgeTargets.Below S n → ∀ xs ys zs,
  _root_.Nonempty (ExtendedMultisetTree S xs ys) →
  ∀ right : ExtendedMultisetTree S ys zs, treeSize right < n → OrdinaryArgs zs →
  _root_.Nonempty (ExtendedMultisetTree S xs zs)

def FullOccurrences : Prop := WeakWeak ∧ WeakStrict ∧ StrictWeak ∧ StrictStrict
end LogicLineages.PersistentMarking.CutOccurrenceTargets
