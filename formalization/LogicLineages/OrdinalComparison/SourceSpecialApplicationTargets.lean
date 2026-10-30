module

public import LogicLineages.OrdinalComparison.SourceSpecialApplicationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSpecialApplicationTargets
open SourceMarkedSyntax SourceMarkedBinding SourceSpecialApplication

def EmptySpecialApplication : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (q : MarkedTerm Symbol arity Γ τ), specialApply (types := []) q .nil = some q

def OriginalVariableBlocked : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (ρ τ : Ty) (types : List Ty)
    (v : Variable Γ (arrows (ρ :: types) τ)) (env : MarkedSubstitution Symbol arity Γ Δ)
    (a : MarkedTerm Symbol arity Δ ρ) (rest : Arguments Symbol arity Δ types),
      applyOriginalWith (.var v) env (.cons a rest) rfl = none

def OriginalLambdaConsumption : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (ρ τ : Ty) (types : List Ty)
    (body : MarkedTerm Symbol arity (ρ :: Γ) (arrows types τ))
    (env : MarkedSubstitution Symbol arity Γ Δ) (a : MarkedTerm Symbol arity Δ ρ)
    (rest : Arguments Symbol arity Δ types),
      applyOriginalWith (.lam body) env (.cons a rest) rfl =
        applyOriginalWith body (extendEnvironment env a) rest rfl

def FunctionalOneShotAppend : Prop :=
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (ρ τ : Ty) (types : List Ty)
    (hd : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity hd))
    (env : MarkedSubstitution Symbol arity Γ Δ) (a : MarkedTerm Symbol arity Δ ρ)
    (rest : Arguments Symbol arity Δ types) (h : headResult hd = arrows (ρ :: types) τ),
      applyOriginalWith (.ordinary hd base) env (.cons a rest) h =
        some (.marked hd τ (substituteArguments base env) (ρ :: types) (.cons a rest))) ∧
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (ρ τ output : Ty)
    (types extraTypes : List Ty) (hd : Head Symbol)
    (base : Arguments Symbol arity Γ (headArguments arity hd)) (extras : Arguments Symbol arity Γ extraTypes)
    (env : MarkedSubstitution Symbol arity Γ Δ) (a : MarkedTerm Symbol arity Δ ρ)
    (rest : Arguments Symbol arity Δ types) (h : output = arrows (ρ :: types) τ),
      applyOriginalWith (.marked hd output base extraTypes extras) env (.cons a rest) h =
        some (.marked hd τ (substituteArguments base env) (extraTypes ++ (ρ :: types))
          (appendArguments (substituteArguments extras env) (.cons a rest))))

def OriginalSpineCounterexample : Prop :=
  specialApply (embed exampleIdentity) (.cons (embed exampleSuccessor) (.cons (embed exampleVariable) .nil)) = none ∧
    ((specialApply (embed exampleIdentity) (.cons (embed exampleSuccessor) .nil)).bind
      (fun q => specialApply q (.cons (embed exampleVariable) .nil))) =
        some (.marked .succ .ground .nil [.ground] (.cons (embed exampleVariable) .nil))

end LogicLineages.OrdinalComparison.Source.SourceSpecialApplicationTargets
