import LogicLineages.PersistentMarking.NumberedWindowTraceBudgetTargets
import LogicLineages.PersistentMarking.LiteralDerivationTree

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationData
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPrimary
open NumberedWindowPreservationTargets

/-- The finite budget is computed on the literal data certificate, with
no search for a favorable numerical realization. The two distinct
original Stat derivations are present and both feed this bound. -/
def budget {S : Spine.Signature} {J : Judgment} (tree : Tree S J) : Nat :=
  match tree with
  | .var _ _ => 0
  | .abs _ _ _ _ _ _ _ _ _ t => budget t
  | .funHead _ _ _ _ _ _ _ _ t => budget t
  | .put _ _ _ _ _ t => budget t + 1
  | .select f _ bs es _ _ _ ds _ _ _ _ _ _ t =>
      budget t + (Spine.ownerCopies f bs es ds).length + 2
  | .fabs _ _ _ _ _ _ _ _ _ _ _ t => budget t + 1
  | .copy _ _ _ _ _ _ _ _ t => budget t + 1
  | .stat _ _ _ _ _ _ _ _ m w => max (budget m) (budget w) + 1
  | .strictIntro _ _ _ _ _ _ _ t => budget t + 1
  | .matchingNil => 0
  | .matchingCons _ _ _ _ _ _ t more => max (budget t) (budget more)
  | .multisetReplace _ _ _ _ _ _ _ _ _ m c => max (budget m) (budget c)
  | .coverageNil _ => 0
  | .coverageCons _ _ _ _ _ _ t more => max (budget t) (budget more)
  | .wholeNil _ _ _ => 0
  | .wholeCons _ _ _ _ _ t more => max (budget t) (budget more)

def AdmittedTrace {S K C τ} {q r : NTerm} (trace : TypedTrace S K C τ q r) : Prop :=
  ∀ p ∈ vertices trace, InWindow S K C τ p

/-- The full declaration-retaining, lexically typed carrier in one
unchanged signature/window/context/result type. -/
def WindowCarrier (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty) :=
  {q : NTerm // InWindow S K C τ q}

/-- Primary classes, not a new equivalence relation or a least-code
enumeration assertion. The existing Primary has genuine refl/symm/trans. -/
def Class (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty) :=
  Quot (fun a b : WindowCarrier S K C τ => Primary S K C τ a.val b.val)

def classOf {S K C τ} (q : WindowCarrier S K C τ) : Class S K C τ :=
  Quot.mk (fun a b : WindowCarrier S K C τ => Primary S K C τ a.val b.val) q

/-- An actual one-step raw witness between representatives of the two
typed primary classes. Equivalence alone is not an edge. -/
def ClassEdge {S K C τ} (x y : Class S K C τ) : Prop :=
  ∃ q r : WindowCarrier S K C τ, classOf q = x ∧ classOf r = y ∧ RawStep S K q.val r.val

/-- The manuscript's positive raw relation on primary classes, resolved
at the unchanged lexical type. There is no reflexive/empty constructor. -/
inductive RS (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty) :
    Class S K C τ → Class S K C τ → Prop where
  | one {x y : Class S K C τ} : ClassEdge x y → RS S K C τ x y
  | more {x y z : Class S K C τ} : ClassEdge x y → RS S K C τ y z → RS S K C τ x z

end LogicLineages.PersistentMarking.NumberedWindowSimulationData
