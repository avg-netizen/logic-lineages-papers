module

public import LogicLineages.OrdinalComparison.SourceSubstitutionSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSubstitutionSupportTargets
open SourceTypeSupport

def ActualSubstitutionSupport : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (s : Substitution Symbol arity Γ Δ) (K : Finset Ty),
      typeSupport t ⊆ K →
      (∀ (σ : Ty) (v : Variable Γ σ), typeSupport (s v) ⊆ K) →
      typeSupport (t.substitute s) ⊆ K

def ActualSubstitutionDepth : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (s : Substitution Symbol arity Γ Δ) (L : Nat),
      (∀ (σ : Ty) (v : Variable Γ σ), lambdaDepth (s v) ≤ L) →
      lambdaDepth t ≤ lambdaDepth (t.substitute s) ∧
      lambdaDepth (t.substitute s) ≤ lambdaDepth t + L

def VariableSubstitutionRenaming : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (ρ : Renaming Γ Δ),
      t.substitute (fun v => Term.var (ρ v)) = t.rename ρ

def TypedBodyOpeningBudget : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (σ τ : Ty)
    (body : Term Symbol arity (σ :: Γ) τ) (ρ : Renaming (σ :: Γ) Δ),
      typeSupport (body.rename ρ) ⊆ typeSupport (Term.lam body) ∧
      lambdaDepth (body.rename ρ) + 1 = lambdaDepth (Term.lam body) ∧
      ∀ used B : Nat, used + lambdaDepth (Term.lam body) ≤ B →
        used + 1 + lambdaDepth (body.rename ρ) ≤ B

end LogicLineages.OrdinalComparison.Source.SourceSubstitutionSupportTargets
