module

public import LogicLineages.NativeModule.PersistentMarking.RefinementSyntaxTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.OwnerRefinementTargets
open Spine

def PrefixOmission : Prop := ∀ S f τ base extras pref,
  PaperTerm S (.marked f τ base extras) τ → Prefix pref extras →
  Refines S (.marked f τ base extras) (.marked f τ base pref)

def Permutation : Prop := ∀ S f τ base extras ds,
  PaperTerm S (.marked f τ base extras) τ → Spine.Permutation extras ds →
  Refines S (.marked f τ base extras) (.marked f τ base ds)

def PrefixExpansion : Prop := ∀ S f τ base extras ps,
  PaperTerm S (.marked f τ base extras) τ → PrefixCopies f base extras ps →
  Refines S (.marked f τ base extras) (.marked f τ base (extras.append ps))

def RefinedCopies : Prop := ∀ S f τ qb qe sb se domains bs,
  Refines S (.marked f τ qb qe) (.marked f τ sb se) →
  PrefixTuple f sb se domains bs →
  _root_.Nonempty (RefinementBasesTree S (ownerCopies f qb qe domains) bs)
end LogicLineages.PersistentMarking.OwnerRefinementTargets
