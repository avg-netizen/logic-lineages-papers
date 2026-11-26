import LogicLineages.PersistentMarking.DecisionInventory
namespace LogicLineages.PersistentMarking.DecisionPorts
open Spine NameBridge DecisionInventory
abbrev Context := List (Option Ty)
def used : Context → Nat
  | [] => 0
  | none::rest => used rest
  | some _::rest => 1 + used rest
def Extends (Γ Δ : Context) : Prop := Γ.length = Δ.length ∧
  ∀ (i : Nat) (σ : Ty), Γ[i]? = some (some σ) → Δ[i]? = some (some σ)
def WellFormed (K : List Ty) (B : Nat) (Γ : Context) : Prop :=
  Γ.length = B ∧ ∀ (i : Nat) (σ : Ty), Γ[i]? = some (some σ) → σ ∈ K

def contexts (K : List Ty) : Nat → List Context
  | 0 => [[]]
  | n+1 => (none :: K.map some).flatMap (fun entry => (contexts K n).map (entry :: ·))
def maxName : List Name → Nat
  | [] => 0
  | (_,x)::xs => max x (maxName xs)
def portName (V : List Name) (i : Nat) : Nat := maxName V + 1 + i
/- Substitution values use the exact slot's stored type, with no restriction
that all used slots be selected, or that assignments be injective. -/
def AtPort (V : List Name) (Γ : Context) (σ : Ty) (q : Expr) : Prop :=
  ∃ i, Γ[i]? = some (some σ) ∧ q = .free σ (portName V i)
def values (V : List Name) (Γ : Context) (σ : Ty) : List Expr :=
  (List.range Γ.length).filterMap fun i =>
    if Γ[i]? = some (some σ) then some (.free σ (portName V i)) else none
end LogicLineages.PersistentMarking.DecisionPorts
