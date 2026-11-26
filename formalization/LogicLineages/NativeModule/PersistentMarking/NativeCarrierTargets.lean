module

public import LogicLineages.NativeModule.PersistentMarking.NativeReduction
public import LogicLineages.NativeModule.PersistentMarking.DecisionInventory

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeCarrierTargets
open Spine NameBridge TypeSupport NativeReduction

def Native (q : Expr) : Prop :=
  ∀ name arity, Head.ranked name arity ∉ DecisionInventory.heads q

def Closed (q : Expr) : Prop := ∀ n, freeOccurs n q = false

def ClosedOrdinary (S : Signature) (q : Expr) (τ : Ty) : Prop :=
  PaperTerm S q τ ∧ Ordinary q ∧ Closed q

def ClosedNative (S : Signature) (q : Expr) (τ : Ty) : Prop :=
  ClosedOrdinary S q τ ∧ Native q

def lifted (K : Expr) : Expr := .lam .ground K

def W (B : Ty) (K U : Expr) : Expr := recTerm B zero (lifted K) U

def qBase (B : Ty) (K U : Expr) : Args := .cons (rec2 B zero (lifted K)) (.cons U .nil)
def c2Base (B : Ty) (K : Expr) : Args := .cons (rec1 B zero) (.cons (lifted K) .nil)
def c1Base (B : Ty) : Args := .cons (.head (.recursor B) .nil) (.cons zero .nil)

def Q (B : Ty) (K U : Expr) (ρ : Ty) : Expr := .marked (.app B B) ρ (qBase B K U) .nil
def c2Extras (B : Ty) (K U : Expr) : Args := .cons (Q B K U B) .nil
def C₂ (B : Ty) (K U : Expr) (ρ : Ty) : Expr :=
  .marked (.app (stepType B) (.arrow B B)) ρ (c2Base B K) (c2Extras B K U)
def c1Extras (B : Ty) (K U : Expr) : Args := .cons (C₂ B K U (stepType B)) (.cons (C₂ B K U B) .nil)
def C₁ (B : Ty) (K U : Expr) (ρ : Ty) : Expr :=
  .marked (.app .ground (.arrow (stepType B) (.arrow B B))) ρ (c1Base B) (c1Extras B K U)
def c0Extras (B : Ty) (K U : Expr) : Args :=
  .cons (C₁ B K U .ground) (.cons (C₁ B K U (stepType B)) (.cons (C₁ B K U B) .nil))
def C₀ (B : Ty) (K U : Expr) (ρ : Ty) : Expr := .marked (.recursor B) ρ .nil (c0Extras B K U)

def Carrier : Prop := ∀ S B P K U,
  ClosedNative S P (.arrow B B) → ClosedNative S K (.arrow B B) → ClosedNative S U B →
  Weak S K P → Included P K →
  ConfinedPair.Strict S (W B K U) U ∧
  ∀ T, ClosedOrdinary S T B → Included T (W B K U) → ConfinedPair.Strict S (W B K U) T →
    ConfinedPair.Strict S (W B K U) (app B B P T)

end LogicLineages.PersistentMarking.NativeCarrierTargets
