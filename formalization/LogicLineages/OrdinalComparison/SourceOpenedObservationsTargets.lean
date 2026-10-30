module
public import LogicLineages.OrdinalComparison.SourceOpenedObservationsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceOpenedObservationsTargets
open SourceTypeSupport SourceLocatedSubterms SourceTypedPorts SourcePortContexts SourceOpenedObservations

def OpenedObservationMembership : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (B : Nat)
    (o : Observation Symbol arity Γ B), o ∈ observations B t ↔
    ValidPorts (typeSupport t) o.ports ∧ ∃ u ∈ collect [] t,
      ∃ h : u.ambient = u.binders ++ Γ, ∃ a : PortMap (portTypes o.ports) u.binders,
        (indices a).Nodup ∧ o.ports.length + lambdaDepth u.body ≤ B ∧ o = openLocated Γ o.ports u h a

def OpenedRootMembership : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (B : Nat), lambdaDepth t ≤ B →
    (⟨[], τ, t⟩ : Observation Symbol arity Γ B) ∈ observations B t

def OpenedPlainChildClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (B : Nat)
    (o v : Observation Symbol arity Γ B), o ∈ observations B t →
      v ∈ plainChildren o → v ∈ observations B t

def OpenedLambdaClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (B : Nat)
    (P : PortContext B) (σ υ : Ty) (body : Term Symbol arity (σ :: (portTypes P ++ Γ)) υ),
    (⟨P, .arrow σ υ, .lam body⟩ : Observation Symbol arity Γ B) ∈ observations B t →
    (∃ i : Fin B, i ∉ P.map Prod.fst) ∧
    ∀ i : Fin B, i ∉ P.map Prod.fst →
      (⟨(i, σ) :: P, υ, body⟩ : Observation Symbol arity Γ B) ∈ observations B t

def OpenedDepthBudget : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (B : Nat)
    (o : Observation Symbol arity Γ B), o ∈ observations B t →
      o.ports.length + lambdaDepth o.body ≤ B

def OpenedTypeSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (B : Nat)
    (o : Observation Symbol arity Γ B), o ∈ observations B t → typeSupport o.body ⊆ typeSupport t
end LogicLineages.OrdinalComparison.Source.SourceOpenedObservationsTargets
