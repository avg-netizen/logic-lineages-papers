module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RecursiveComparison LiteralContexts RenamingEquivariance

def SubstitutionCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Γ' Δ Δ' : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ)
    (r : Renaming Γ Γ') (s : Renaming Δ Δ')
    (env : MarkedSubstitution Symbol arity Γ Δ) (env' : MarkedSubstitution Symbol arity Γ' Δ'),
    (∀ {σ} (v : Variable Γ σ),env' (r v)=renameTerm (env v) s) →
    substituteTerm (renameTerm q r) env'=renameTerm (substituteTerm q env) s

def OriginalApplyCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Γ' Δ Δ' : List Ty) (σ τ : Ty) (types : List Ty)
    (q : MarkedTerm Symbol arity Γ σ) (args : Arguments Symbol arity Δ types)
    (r : Renaming Γ Γ') (s : Renaming Δ Δ')
    (env : MarkedSubstitution Symbol arity Γ Δ) (env' : MarkedSubstitution Symbol arity Γ' Δ')
    (suffix : σ=arrows types τ),
    (∀ {υ} (v : Variable Γ υ),env' (r v)=renameTerm (env v) s) →
    applyOriginalWith (renameTerm q r) env' (renameArguments args s) suffix =
      (applyOriginalWith q env args suffix).map (fun out => renameTerm out s)

def WeakCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ Δ : List Ty) (ρ : Renaming Γ Δ) (s t : Packed Symbol arity Γ),
    Weak Symbol arity above Γ s t → Weak Symbol arity above Δ (renamePacked ρ s) (renamePacked ρ t)

def StrictCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ Δ : List Ty) (ρ : Renaming Γ Δ) (s t : Packed Symbol arity Γ),
    Strict Symbol arity above Γ s t → Strict Symbol arity above Δ (renamePacked ρ s) (renamePacked ρ t)

def WeakMatchCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ Δ : List Ty) (ρ : Renaming Γ Δ) (ss ts : List (Packed Symbol arity Γ)),
    WeakMatch Symbol arity above Γ ss ts → WeakMatch Symbol arity above Δ (ss.map (renamePacked ρ)) (ts.map (renamePacked ρ))

def StrictMultisetCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ Δ : List Ty) (ρ : Renaming Γ Δ) (ss ts : List (Packed Symbol arity Γ)),
    StrictMultiset Symbol arity above Γ ss ts → StrictMultiset Symbol arity above Δ (ss.map (renamePacked ρ)) (ts.map (renamePacked ρ))

def ReplacementMatchCovariance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ Δ : List Ty) (ρ : Renaming Γ Δ) (ss ts : List (Packed Symbol arity Γ)),
    ReplacementMatch Symbol arity above Γ ss ts → ReplacementMatch Symbol arity above Δ (ss.map (renamePacked ρ)) (ts.map (renamePacked ρ))

def RenamedContextStrictClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Ξ Δ Γ : List Ty) (υ τ : Ty) (ρ : Renaming Ξ Δ) (C : Context Symbol arity Δ υ Γ τ)
    (s t : Term Symbol arity Ξ υ), Strict Symbol arity above Ξ ⟨υ,embed s⟩ ⟨υ,embed t⟩ →
    Strict Symbol arity above Γ ⟨τ,embed (plug C (s.rename ρ))⟩ ⟨τ,embed (plug C (t.rename ρ))⟩

def RenamedConfinedContextClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Ξ Δ Γ : List Ty) (υ τ : Ty) (ρ : Renaming Ξ Δ) (C : Context Symbol arity Δ υ Γ τ)
    (s t : Term Symbol arity Ξ υ), ConfinedStrict above s t →
    ConfinedStrict above (plug C (s.rename ρ)) (plug C (t.rename ρ))

end LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceTargets
