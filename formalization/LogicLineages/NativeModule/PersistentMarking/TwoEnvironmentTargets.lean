module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedComparison
public import LogicLineages.NativeModule.PersistentMarking.FreeCovarianceTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.TwoEnvironmentTargets
open Spine

def Related (S : Signature) (γ δ : FreeMap) : Prop := ∀ σ x, ExtendedWeak S (γ σ x) (δ σ x)
def Weak : Prop := ∀ S γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  ∀ s t, ExtendedWeak S s t → ExtendedWeak S (freeSub γ 0 s) (freeSub δ 0 t)
def Strict : Prop := ∀ S γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  ∀ s t, ExtendedStrict S s t → ExtendedStrict S (freeSub γ 0 s) (freeSub δ 0 t)
def Matching : Prop := ∀ S γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  ∀ ss ts, _root_.Nonempty (ExtendedMatchingTree S ss ts) →
    _root_.Nonempty (ExtendedMatchingTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))
def Multiset : Prop := ∀ S γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  ∀ ss ts, _root_.Nonempty (ExtendedMultisetTree S ss ts) →
    _root_.Nonempty (ExtendedMultisetTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))
def Coverage : Prop := ∀ S γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  ∀ ss ts, _root_.Nonempty (ExtendedCoverageTree S ss ts) →
    _root_.Nonempty (ExtendedCoverageTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))
def Whole : Prop := ∀ S γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  ∀ f base extras ts, _root_.Nonempty (ExtendedWholeTree S f base extras ts) →
    _root_.Nonempty (ExtendedWholeTree S f (freeSubArgs γ 0 base) (freeSubArgs γ 0 extras) (freeSubArgs δ 0 ts))
def Ordered : Prop := ∀ S γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  ∀ ss ts, _root_.Nonempty (ExtendedOrderedTree S ss ts) →
    _root_.Nonempty (ExtendedOrderedTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))

/-- Full auxiliary weak/strict and every actual companion-list judgment. -/
def FullTwoEnvironments : Prop := Weak ∧ Strict ∧ Matching ∧ Multiset ∧ Coverage ∧ Whole ∧ Ordered
end LogicLineages.PersistentMarking.TwoEnvironmentTargets
