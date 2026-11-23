import LogicLineages.PersistentMarking.NativeClosedApplication

namespace LogicLineages.PersistentMarking.NativeStructuralRealizationSyntax
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets

/-- Typed de Bruijn occurrence in the same nearest-binder order as Spine. -/
inductive Var : List SemanticType → SemanticType → Type where
  | here : Var (A :: Γ) A
  | there : Var Γ A → Var (D :: Γ) A

def Var.index : Var Γ A → Nat
  | .here => 0
  | .there i => i.index + 1

/-- Typing evidence for a literal source fragment, not a new reduction
syntax. Constants are supplied individually as actual closed expressions. -/
inductive Fragment (C : SemanticType → Type) : List SemanticType → SemanticType → Type where
  | var {Γ : List SemanticType} {A : SemanticType} : Var Γ A → Fragment C Γ A
  | app {Γ : List SemanticType} (A D : SemanticType) : Fragment C Γ (.arrow A D) → Fragment C Γ A → Fragment C Γ D
  | lam {Γ : List SemanticType} {D : SemanticType} (A : SemanticType) : Fragment C (A :: Γ) D → Fragment C Γ (.arrow A D)
  | literal {Γ : List SemanticType} {A : SemanticType} : C A → Fragment C Γ A

abbrev Literals (S : Signature) (C : SemanticType → Type) :=
  (A : SemanticType) → C A → ClosedNativeTerm S (actualType A)

def Fragment.raw (lit : Literals S C) : {Γ : List SemanticType} → {A : SemanticType} →
    Fragment C Γ A → Expr
  | _, A, .var i => .bound (actualType A) i.index
  | _, _, .app A D f u => NativeReduction.app (actualType A) (actualType D) (f.raw lit) (u.raw lit)
  | _, _, .lam A body => .lam (actualType A) (body.raw lit)
  | _, A, .literal k => (lit A k).val

def rawContext : List SemanticType → BoundContext
  | [] => EmptyContext
  | A :: Γ => (rawContext Γ).push (actualType A)

/-- One original closed operand at every occurrence of the typed binder list. -/
inductive ClosedEnv (S : Signature) : List SemanticType → Type where
  | nil : ClosedEnv S []
  | cons {Γ : List SemanticType} {A : SemanticType} : ClosedNativeTerm S (actualType A) → ClosedEnv S Γ → ClosedEnv S (A :: Γ)

def ClosedEnv.args : ClosedEnv S Γ → Args
  | .nil => .nil
  | .cons q ρ => .cons q.val ρ.args

def ClosedEnv.lookup (i : Var Γ A) (ρ : ClosedEnv S Γ) : ClosedNativeTerm S (actualType A) :=
  match i, ρ with
  | .here, .cons q _ => q
  | .there i, .cons _ ρ => lookup i ρ

def ExactLiteralStructuralTyping : Prop :=
  ∀ (S : Signature) (C : SemanticType → Type) (lit : Literals S C)
    (Γ : List SemanticType) (A : SemanticType) (t : Fragment C Γ A),
    Typed (rawContext Γ) (t.raw lit) (actualType A)

end LogicLineages.PersistentMarking.NativeStructuralRealizationSyntax
