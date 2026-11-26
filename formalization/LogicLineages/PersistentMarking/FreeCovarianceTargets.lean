import LogicLineages.PersistentMarking.FreeSubstitution

namespace LogicLineages.PersistentMarking.FreeCovarianceTargets
open Spine

def ShiftCancellation : Prop :=
  ∀ (vs : Args) (k c : Nat) (t : Expr),
    substitute vs (k+c) (shift (k+vs.length) c t) = shift k c t

def ShiftArgsCancellation : Prop :=
  ∀ (vs : Args) (k c : Nat) (ts : Args),
    substituteArgs vs (k+c) (shiftArgs (k+vs.length) c ts) = shiftArgs k c ts

def FreeShift : Prop :=
  ∀ (θ : FreeMap) (k d : Nat) (t : Expr),
    freeSub θ (k+d) (shift k d t) = shift k d (freeSub θ d t)

def FreeShiftArgs : Prop :=
  ∀ (θ : FreeMap) (k d : Nat) (ts : Args),
    freeSubArgs θ (k+d) (shiftArgs k d ts) = shiftArgs k d (freeSubArgs θ d ts)

def ParallelComposition : Prop :=
  ∀ (θ : FreeMap) (vs : Args) (d : Nat) (q : Expr),
    freeSub θ d (substitute vs d q) =
      substitute (freeSubArgs θ 0 vs) d (freeSub θ (d+vs.length) q)

def ParallelArgsComposition : Prop :=
  ∀ (θ : FreeMap) (vs : Args) (d : Nat) (qs : Args),
    freeSubArgs θ d (substituteArgs vs d qs) =
      substituteArgs (freeSubArgs θ 0 vs) d (freeSubArgs θ (d+vs.length) qs)

def AnnotationPreserves : Prop :=
  ∀ (Γ : BoundContext) (θ : FreeMap), FreeMapTyped Γ θ →
    ∀ (d : Nat) (q : Expr), (freeSub θ d q).type = q.type

def SuccessfulCallCovariance : Prop :=
  ∀ (Γ : BoundContext) (θ : FreeMap) (q : Expr) (σ : Ty)
    (args : Args) (τ : Ty) (r : Expr),
    FreeMapTyped Γ θ → Typed Γ q σ → CallTyped Γ σ args τ →
    apply q args = some r →
    apply (freeSub θ 0 q) (freeSubArgs θ 0 args) = some (freeSub θ 0 r)

end LogicLineages.PersistentMarking.FreeCovarianceTargets
