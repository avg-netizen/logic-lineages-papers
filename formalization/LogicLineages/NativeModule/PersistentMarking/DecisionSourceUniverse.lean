module

public import LogicLineages.NativeModule.PersistentMarking.DecisionObservations

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionSourceUniverse
open Spine NameBridge DecisionInventory DecisionPorts

def Closed (K : List Ty) : Prop := ∀ σ, σ ∈ K → ∀ τ, τ ∈ TypeSupport.subtypes σ → τ ∈ K

def AllowedName (V : List Name) (Γ : Context) (n : Name) : Prop :=
  n ∈ V ∨ AtPort V Γ n.1 (.free n.1 n.2)

def Universe (K : List Ty) (V : List Name) (H : List Head) (Γ : Context) (q : Expr) : Prop :=
  (∀ σ, σ ∈ auxiliarySupport q → σ ∈ K) ∧
  (∀ f, f ∈ heads q → f ∈ H) ∧
  (∀ name, freeOccurs name q = true → AllowedName V Γ name)

def ArgsUniverse (K : List Ty) (V : List Name) (H : List Head) (Γ : Context) : Args → Prop
  | .nil => True
  | .cons q qs => Universe K V H Γ q ∧ ArgsUniverse K V H Γ qs
end LogicLineages.PersistentMarking.DecisionSourceUniverse
