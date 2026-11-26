import LogicLineages.PersistentMarking.RefinementSyntaxTargets
namespace LogicLineages.PersistentMarking.ConservativeTargets
open Spine

def Weak : Prop := ∀ S q s t, Refines S q s → ExtendedWeak S s t → Ordinary t → Spine.Weak S q t

def Strict : Prop := ∀ S q s t, Refines S q s → ExtendedStrict S s t → Ordinary t → Spine.Strict S q t

def Matching : Prop := ∀ S qs ss ts,
  _root_.Nonempty (RefinementBasesTree S qs ss) → _root_.Nonempty (ExtendedMatchingTree S ss ts) →
  OrdinaryArgs ts → Spine.Matching S qs ts

def Multiset : Prop := ∀ S qs ss ts,
  _root_.Nonempty (RefinementBasesTree S qs ss) → _root_.Nonempty (ExtendedMultisetTree S ss ts) →
  OrdinaryArgs ts → Spine.Multiset S qs ts

def Coverage : Prop := ∀ S qs ss ts,
  _root_.Nonempty (RefinementBasesTree S qs ss) → _root_.Nonempty (ExtendedCoverageTree S ss ts) →
  OrdinaryArgs ts → Spine.Coverage S qs ts

/-- Complete ordinary-target elimination, including the strict and three
list-judgment companions explicitly asserted in the source. -/
def FullConservative : Prop := Weak ∧ Strict ∧ Matching ∧ Multiset ∧ Coverage
end LogicLineages.PersistentMarking.ConservativeTargets
