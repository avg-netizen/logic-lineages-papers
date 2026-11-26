module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryClassList

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryClassListTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowFiniteSaturation NumberedWindowPrimaryClassList
universe u

/-- The same bound works for any finite carrier list, including duplicates.
The concrete class algorithm instantiates the true literal equality bit. -/
def BoundedFixedPoint : Prop :=
  ∀ {α : Type u} (vertices : List α) (same edge : α → α → Bool) (seed : α),
    EqualityTest same →
    advance vertices same edge (saturate vertices same edge seed) =
      saturate vertices same edge seed

def ExactBoundedGraphReach : Prop :=
  ∀ {α : Type u} (vertices : List α) (same edge : α → α → Bool) (seed v : α),
    EqualityTest same →
    (v ∈ saturate vertices same edge seed ↔ GraphReach vertices edge seed v)

def AbstractExactPrimaryClassList : Prop :=
  ∀ S K C τ Q R, DecisionSourceUniverse.Closed K → InWindow S K C τ Q →
    (R ∈ classList S K C τ Q ↔ Primary S K C τ Q R)

/-- Concrete finite binder stacks give exact original Primary membership.
No independent target typing/window/cover/reachability premise. -/
def ExactFinitePrimaryClassList : Prop :=
  ∀ S K Γ τ Q R, DecisionSourceUniverse.Closed K →
    InWindow S K (Spine.BoundContext.«prefix» Γ Spine.EmptyContext) τ Q →
    (R ∈ finiteClassList S K Γ τ Q ↔
      Primary S K (Spine.BoundContext.«prefix» Γ Spine.EmptyContext) τ Q R)

def ExactFinitePrimaryDecision : Prop :=
  ∀ S K Γ τ Q R, DecisionSourceUniverse.Closed K →
    InWindow S K (Spine.BoundContext.«prefix» Γ Spine.EmptyContext) τ Q →
    (primaryBit S K Γ τ Q R = true ↔
      Primary S K (Spine.BoundContext.«prefix» Γ Spine.EmptyContext) τ Q R)

end LogicLineages.PersistentMarking.NumberedWindowPrimaryClassListTargets
