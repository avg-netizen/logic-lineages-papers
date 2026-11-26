module

public import LogicLineages.NativeModule.PersistentMarking.TypeSupportTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.Grafting
open Spine NameBridge TypeSupport

def singleMap (σ : Ty) (x : Nat) (p : Expr) : FreeMap := fun τ y =>
  if (τ,y) = (σ,x) then p else .free τ y

def singleNamedMap (σ : Ty) (x : Nat) (p : Term) : NamedMap := fun τ y =>
  if (τ,y) = (σ,x) then p else .var τ y

def NamedMapTyped (η : NamedMap) : Prop := ∀ σ x, NamedTyped (η σ x) σ
end LogicLineages.PersistentMarking.Grafting
