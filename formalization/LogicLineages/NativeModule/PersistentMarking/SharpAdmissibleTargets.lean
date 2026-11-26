module

public import LogicLineages.NativeModule.PersistentMarking.RefinementSyntaxTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.SharpAdmissibleTargets
open Spine

def Weak : Prop := ∀ S q s t, Refines S q s → ExtendedWeak S s t → ExtendedWeak S q t

def Strict : Prop := ∀ S q s t, Refines S q s → ExtendedStrict S s t → ExtendedStrict S q t

def Matching : Prop := ∀ S qs ss ts,
  _root_.Nonempty (RefinementBasesTree S qs ss) → _root_.Nonempty (ExtendedMatchingTree S ss ts) →
  _root_.Nonempty (ExtendedMatchingTree S qs ts)

def Multiset : Prop := ∀ S qs ss ts,
  _root_.Nonempty (RefinementBasesTree S qs ss) → _root_.Nonempty (ExtendedMultisetTree S ss ts) →
  _root_.Nonempty (ExtendedMultisetTree S qs ts)

def Coverage : Prop := ∀ S qs ss ts,
  _root_.Nonempty (RefinementBasesTree S qs ss) → _root_.Nonempty (ExtendedCoverageTree S ss ts) →
  _root_.Nonempty (ExtendedCoverageTree S qs ts)

/-- Complete unrestricted-target refinement admissibility, including the
strict and three occurrence-list companions asserted in the source. -/
def FullAdmissible : Prop := Weak ∧ Strict ∧ Matching ∧ Multiset ∧ Coverage
end LogicLineages.PersistentMarking.SharpAdmissibleTargets
