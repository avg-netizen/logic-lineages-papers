import LogicLineages.PersistentMarking.SpineMarking
namespace LogicLineages.PersistentMarking.SpineMarkingTargets
open Spine

def PersistentSuccess : Prop :=
  ∀ q r, mark q = some r → mark r = some r

def HeadmarkIdempotent : Prop := ∀ q, headmark (headmark q) = headmark q

def MarkHeadmark : Prop := ∀ q r, mark q = some r → headmark q = r

def MarkTyped : Prop :=
  ∀ Γ q σ r, Typed Γ q σ → mark q = some r → Typed Γ r σ

def HeadmarkTyped : Prop := ∀ Γ q σ, Typed Γ q σ → Typed Γ (headmark q) σ

def SuccessfulMarkCovariance : Prop :=
  ∀ (θ : FreeMap) (d : Nat) (q r : Expr), mark q = some r →
    mark (freeSub θ d q) = some (freeSub θ d r)

/-- Images inhabit the actual outside Γ. The source and result retain the
literal binder prefix; no assumed lifted-image compatibility is an endpoint. -/
def FreeSubTypedUnderBinders : Prop :=
  ∀ Γ θ, FreeMapTyped Γ θ → ∀ (types : List Ty) q σ,
    Typed (BoundContext.«prefix» types Γ) q σ →
    Typed (BoundContext.«prefix» types Γ) (freeSub θ types.length q) σ

def FreeSubTyped : Prop :=
  ∀ Γ θ, FreeMapTyped Γ θ → ∀ q σ, Typed Γ q σ → Typed Γ (freeSub θ 0 q) σ

end LogicLineages.PersistentMarking.SpineMarkingTargets
