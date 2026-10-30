module

public import LogicLineages.OrdinalComparison.SourceTypeSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypeSupportTargets
open SourceTypeSupport

def ActualResultSupport : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ), τ ∈ typeSupport t

def SubtypeClosedSupport : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (σ : Ty), σ ∈ typeSupport t →
      ∀ υ : Ty, υ ∈ σ.subtypes → υ ∈ typeSupport t

def SupportDepthRenaming : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (ρ : Renaming Γ Δ),
      typeSupport (t.rename ρ) = typeSupport t ∧ lambdaDepth (t.rename ρ) = lambdaDepth t

def LiteralBinderSupport : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (σ τ : Ty)
    (body : Term Symbol arity (σ :: Γ) τ),
      typeSupport (Term.lam body) = (Ty.arrow σ τ).subtypes.toFinset ∪ typeSupport body ∧
      σ.subtypes.toFinset ⊆ typeSupport (Term.lam body) ∧
      typeSupport body ⊆ typeSupport (Term.lam body) ∧
      lambdaDepth (Term.lam body) = lambdaDepth body + 1

def LiteralRankedSupport : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (s : Symbol)
    (args : Fin (arity s) → Term Symbol arity Γ .ground),
      typeSupport (Term.ranked s args) = {Ty.ground} ∪
        Finset.univ.biUnion (fun i => typeSupport (args i)) ∧
      lambdaDepth (Term.ranked s args) = Finset.univ.sup (fun i => lambdaDepth (args i))

end LogicLineages.OrdinalComparison.Source.SourceTypeSupportTargets
