import LogicLineages.PersistentMarking.NativeStructuralRealizationClosingProof

namespace LogicLineages.PersistentMarking.NativeStructuralRealizationTargets
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeStructuralRealizationSyntax NativeStructuralRealizationClosingProof

universe u

/-- All functions, without monotonicity or continuity assumptions. Here the
base can later be countable ordinals; this file does not load ordinal data. -/
def Value (Base : Type u) : SemanticType → Type u
  | .base => Base
  | .arrow A D => Value Base A → Value Base D

inductive ValueEnv (Base : Type u) : List SemanticType → Type u where
  | nil : ValueEnv Base []
  | cons : Value Base A → ValueEnv Base Γ → ValueEnv Base (A :: Γ)

def ValueEnv.lookup (i : Var Γ A) (θ : ValueEnv Base Γ) : Value Base A :=
  match i, θ with
  | .here, .cons x _ => x
  | .there i, .cons _ θ => lookup i θ

abbrev Meanings (Base : Type u) (C : SemanticType → Type) :=
  (A : SemanticType) → C A → Value Base A

def denote (meaning : Meanings Base C) :
    {Γ : List SemanticType} → {A : SemanticType} → Fragment C Γ A → ValueEnv Base Γ → Value Base A
  | _, _, .var i, θ => θ.lookup i
  | _, _, .app _ _ f u, θ => (denote meaning f θ) (denote meaning u θ)
  | _, _, .lam _ t, θ => fun x => denote meaning t (.cons x θ)
  | _, A, .literal k, _ => meaning A k

abbrev Relation (S : Signature) (Base : Type u) :=
  (A : SemanticType) → ClosedNativeTerm S (actualType A) → Value Base A → Prop

def ArrowRule (R : Relation S Base) : Prop :=
  ∀ (A D : SemanticType) (f : ClosedNativeTerm S (actualType (.arrow A D))) (v : Value Base (.arrow A D)),
    R (.arrow A D) f v ↔
      ∀ (x : Value Base A) (u : ClosedNativeTerm S (actualType A)),
        R A u x → R D (applyClosed f u) (v x)

def Backward (R : Relation S Base) : Prop :=
  ∀ (A : SemanticType) (target source : ClosedNativeTerm S (actualType A)) (v : Value Base A),
    NativeBelow target source → R A target v → R A source v

def Respects (R : Relation S Base) (ρ : ClosedEnv S Γ) (θ : ValueEnv Base Γ) : Prop :=
  ∀ (A : SemanticType) (i : Var Γ A), R A (ρ.lookup i) (θ.lookup i)

def ExactStructuralNativeRealization : Prop :=
  ∀ (Base : Type u) (S : Signature) (C : SemanticType → Type)
    (lit : Literals S C) (meaning : Meanings Base C) (R : Relation S Base),
    ArrowRule R → Backward R →
    (∀ A (k : C A), R A (lit A k) (meaning A k)) →
    ∀ (Γ : List SemanticType) (A : SemanticType) (t : Fragment C Γ A)
      (ρ : ClosedEnv S Γ) (θ : ValueEnv Base Γ),
      Respects R ρ θ → R A (instantiate lit t ρ) (denote meaning t θ)

end LogicLineages.PersistentMarking.NativeStructuralRealizationTargets
