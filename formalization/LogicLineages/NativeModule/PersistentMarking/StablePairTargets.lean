module

public import LogicLineages.NativeModule.PersistentMarking.ConfinedPair

@[expose] public section

namespace LogicLineages.PersistentMarking.StablePairTargets
open Spine StructuralContext

def WeakReflexive : Prop := ∀ S q τ, PaperTerm S q τ → Ordinary q → ConfinedPair.Weak S q q
def WeakTransitive : Prop := ∀ S s t u, ConfinedPair.Weak S s t → ConfinedPair.Weak S t u → ConfinedPair.Weak S s u
def StrictIncluded : Prop := ∀ S s t, ConfinedPair.Strict S s t → ConfinedPair.Weak S s t
def StrictTransitive : Prop := ∀ S s t u, ConfinedPair.Strict S s t → ConfinedPair.Strict S t u → ConfinedPair.Strict S s u
def WeakStrict : Prop := ∀ S s t u, ConfinedPair.Weak S s t → ConfinedPair.Strict S t u → ConfinedPair.Strict S s u
def StrictWeak : Prop := ∀ S s t u, ConfinedPair.Strict S s t → ConfinedPair.Weak S t u → ConfinedPair.Strict S s u

def WeakSubstitution : Prop := ∀ S s t θ, ConfinedPair.Weak S s t →
  StructuralStabilityTargets.OrdinaryMap S θ → ConfinedPair.Weak S (freeSub θ 0 s) (freeSub θ 0 t)
def StrictSubstitution : Prop := ∀ S s t θ, ConfinedPair.Strict S s t →
  StructuralStabilityTargets.OrdinaryMap S θ → ConfinedPair.Strict S (freeSub θ 0 s) (freeSub θ 0 t)

def WeakContext : Prop := ∀ S C σ τ s t, ContextTyped S C σ τ →
  PaperTerm S s σ → PaperTerm S t σ → ConfinedPair.Weak S s t → ConfinedPair.Weak S (fill C s) (fill C t)
def StrictContext : Prop := ∀ S C σ τ s t, ContextTyped S C σ τ →
  PaperTerm S s σ → PaperTerm S t σ → ConfinedPair.Strict S s t → ConfinedPair.Strict S (fill C s) (fill C t)

def FullStablePair : Prop := WeakReflexive ∧ WeakTransitive ∧ StrictIncluded ∧ StrictTransitive ∧
  WeakStrict ∧ StrictWeak ∧ WeakSubstitution ∧ StrictSubstitution ∧ WeakContext ∧ StrictContext
end LogicLineages.PersistentMarking.StablePairTargets
