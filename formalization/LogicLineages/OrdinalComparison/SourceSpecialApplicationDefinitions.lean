module

public import LogicLineages.OrdinalComparison.SourceMarkedBindingDefinitions

@[expose] public section
/-! Paper06 simultaneous application inspects the ORIGINAL lambda spine.
In particular a remaining original variable blocks, even if substitution
would replace it by a functional head. Equality arguments below express only
literal suffix typing; they do not assert comparison/semantic correctness. -/
namespace LogicLineages.OrdinalComparison.Source.SourceSpecialApplication
open SourceMarkedSyntax SourceMarkedBinding

def arrows : List Ty → Ty → Ty
  | [], τ => τ
  | σ :: types, τ => .arrow σ (arrows types τ)

def extendEnvironment {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {σ : Ty}
    (s : MarkedSubstitution Symbol arity Γ Δ) (a : MarkedTerm Symbol arity Δ σ) :
    MarkedSubstitution Symbol arity (σ :: Γ) Δ
  | _, .here => a
  | _, .there v => s v

def transportTerm {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (h : σ = τ) (q : MarkedTerm Symbol arity Γ σ) : MarkedTerm Symbol arity Γ τ :=
  Eq.mp (congrArg (MarkedTerm Symbol arity Γ) h) q

def applyOriginalWith {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) :
    {Δ : List Ty} → {types : List Ty} → {τ : Ty} →
    MarkedSubstitution Symbol arity Γ Δ → Arguments Symbol arity Δ types →
      σ = arrows types τ → Option (MarkedTerm Symbol arity Δ τ) :=
  fun {Δ} {types} {τ} => match q with
  | .var v => fun env args =>
      match args with
      | .nil => fun h => some (transportTerm h (env v))
      | .cons _ _ => fun _ => none
  | .lam body => fun env args =>
      match args with
      | .nil => fun h => some (transportTerm h (substituteTerm (.lam body) env))
      | .cons a rest => fun h =>
          applyOriginalWith body (extendEnvironment env (transportTerm (Ty.arrow.inj h).1.symm a)) rest
            (Ty.arrow.inj h).2
  | .ordinary hd base => fun env args =>
      match args with
      | .nil => fun h => some (transportTerm h (substituteTerm (.ordinary hd base) env))
      | .cons a rest => fun _ =>
          some (.marked hd τ (substituteArguments base env) _ (.cons a rest))
  | .marked hd output base extraTypes extras => fun env args =>
      match args with
      | .nil => fun h => some (transportTerm h (substituteTerm (.marked hd output base extraTypes extras) env))
      | .cons a rest => fun _ =>
          some (.marked hd τ (substituteArguments base env) _
            (appendArguments (substituteArguments extras env) (.cons a rest)))

def specialApply {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ (arrows types τ)) (args : Arguments Symbol arity Γ types) :
    Option (MarkedTerm Symbol arity Γ τ) :=
  applyOriginalWith q (τ := τ) (fun v => .var v) args rfl

abbrev exampleT : Ty := .arrow .ground .ground
abbrev NativeTerm (Γ : List Ty) (τ : Ty) := Term Empty (fun _ => 0) Γ τ

def exampleIdentity : NativeTerm [.ground] (.arrow exampleT exampleT) := .lam (.var .here)
def exampleSuccessor : NativeTerm [.ground] exampleT := .succC
def exampleVariable : NativeTerm [.ground] .ground := .var .here

end LogicLineages.OrdinalComparison.Source.SourceSpecialApplication
