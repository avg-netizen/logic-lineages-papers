module

public import LogicLineages.OrdinalComparison.SourceMarkedSyntaxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMarkedBinding
open SourceMarkedSyntax

mutual
def renameTerm {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (ρ : Renaming Γ Δ) : MarkedTerm Symbol arity Δ τ :=
  match q with
  | .var v => .var (ρ v)
  | .lam body => .lam (renameTerm body ρ.lift)
  | .ordinary h args => .ordinary h (renameArguments args ρ)
  | .marked h output args extraTypes extras =>
      .marked h output (renameArguments args ρ) extraTypes (renameArguments extras ρ)
def renameArguments {Symbol : Type} {arity : Symbol → Nat} {Γ Δ types : List Ty}
    (args : Arguments Symbol arity Γ types) (ρ : Renaming Γ Δ) : Arguments Symbol arity Δ types :=
  match args with
  | .nil => .nil
  | .cons q rest => .cons (renameTerm q ρ) (renameArguments rest ρ)
end

abbrev MarkedSubstitution (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) :=
  ∀ {σ : Ty}, Variable Γ σ → MarkedTerm Symbol arity Δ σ

def liftSubstitution {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (s : MarkedSubstitution Symbol arity Γ Δ) : MarkedSubstitution Symbol arity (τ :: Γ) (τ :: Δ)
  | _, .here => .var .here
  | _, .there v => renameTerm (s v) (Renaming.weaken Δ τ)

mutual
def substituteTerm {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (s : MarkedSubstitution Symbol arity Γ Δ) :
    MarkedTerm Symbol arity Δ τ :=
  match q with
  | .var v => s v
  | .lam body => .lam (substituteTerm body (liftSubstitution s))
  | .ordinary h args => .ordinary h (substituteArguments args s)
  | .marked h output args extraTypes extras =>
      .marked h output (substituteArguments args s) extraTypes (substituteArguments extras s)
def substituteArguments {Symbol : Type} {arity : Symbol → Nat} {Γ Δ types : List Ty}
    (args : Arguments Symbol arity Γ types) (s : MarkedSubstitution Symbol arity Γ Δ) :
    Arguments Symbol arity Δ types :=
  match args with
  | .nil => .nil
  | .cons q rest => .cons (substituteTerm q s) (substituteArguments rest s)
end

def appendArguments {Symbol : Type} {arity : Symbol → Nat} {Γ xs ys : List Ty}
    (a : Arguments Symbol arity Γ xs) (b : Arguments Symbol arity Γ ys) :
    Arguments Symbol arity Γ (xs ++ ys) :=
  match a with
  | .nil => b
  | .cons q rest => .cons q (appendArguments rest b)

end LogicLineages.OrdinalComparison.Source.SourceMarkedBinding
