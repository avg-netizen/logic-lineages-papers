import LogicLineages.PersistentMarking.SubstitutionTargets
namespace LogicLineages.PersistentMarking.InsertionTargets
open Spine

def InsertedAtDepth : Prop := ∀ v rest σ depth,
  substitute (.cons v rest) depth (.bound σ depth) = shift depth 0 v
def RetainedLocalIndex : Prop := ∀ values σ i depth, i < depth →
  substitute values depth (.bound σ i) = .bound σ i
/-- The equation needed to lift an arbitrary simultaneous substitution
through one retained binder, including out-of-block indices. -/
def BoundUnderBinder : Prop := ∀ values σ i depth,
  substitute values (depth+1) (.bound σ (i+1)) =
    shift 1 0 (substitute values depth (.bound σ i))
end LogicLineages.PersistentMarking.InsertionTargets
