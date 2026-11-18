import LogicLineages.PersistentMarking.SpineSyntax

namespace LogicLineages.PersistentMarking.SpineTargets
open Spine

def EmptyCall : Prop := ∀ q, apply q .nil = some q
def FreeBlocks : Prop := ∀ σ x a rest, apply (.free σ x) (.cons a rest) = none
def BoundBlocks : Prop := ∀ σ i a rest, apply (.bound σ i) (.cons a rest) = none
/-- Explicit capture avoidance: inserting outer bound0 under one retained
lambda changes the inserted index to1, while retained bound0 stays bound0. -/
def BinderCaptureAvoidance : Prop := ∀ σ τ,
  substitute (.cons (.bound σ 0) .nil) 0
    (.lam τ (.bound σ 1)) = .lam τ (.bound σ 1)
def RetainedBinder : Prop := ∀ τ v,
  substitute (.cons v .nil) 0 (.lam τ (.bound τ 0)) =
    .lam τ (.bound τ 0)
/-- The printed obstruction with actual native successor as functional head. -/
def IdentityFunctional : Expr := .lam (.arrow .ground .ground)
  (.bound (.arrow .ground .ground) 0)
def Successor : Expr := .head .succ .nil
def GroundVariable : Expr := .free .ground 0
def FullBlocked : Prop := apply IdentityFunctional
  (.cons Successor (.cons GroundVariable .nil)) = none
def StagedSucceeds : Prop :=
  ((apply IdentityFunctional (.cons Successor .nil)).bind
    (fun q => apply q (.cons GroundVariable .nil))) =
  some (.marked .succ .ground .nil (.cons GroundVariable .nil))
end LogicLineages.PersistentMarking.SpineTargets
