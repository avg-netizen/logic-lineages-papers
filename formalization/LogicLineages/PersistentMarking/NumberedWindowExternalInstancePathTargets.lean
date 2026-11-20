import LogicLineages.PersistentMarking.NumberedWindowExternalInstance
import LogicLineages.PersistentMarking.NumberedWindowRules

namespace LogicLineages.PersistentMarking.NumberedWindowExternalInstancePathTargets
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowSimulationData NumberedWindowExternalInstance

def InstanceClassEdgeOrEqual : Prop :=
  ∀ S K (C : BoundContext) σ τ (hk : DecisionSourceUniverse.Closed K)
    (v w : Class S K (C.push σ) τ) (u : Class S K C σ),
    ClassEdge v w → ClassEdge (instanceClass hk v u) (instanceClass hk w u) ∨
      instanceClass hk v u = instanceClass hk w u

def FreeInstancePreservesPositive : Prop :=
  ∀ S K (C : BoundContext) σ τ (hk : DecisionSourceUniverse.Closed K)
    (v w : Class S K (C.push σ) τ) (u : WindowCarrier S K C σ) i,
    u.val = .free σ i → RS S K (C.push σ) τ v w →
      RS S K C τ (instanceClass hk v (classOf u)) (instanceClass hk w (classOf u))

def FreeInstanceReflectsAccessibility : Prop :=
  ∀ S K (C : BoundContext) σ τ (hk : DecisionSourceUniverse.Closed K)
    (v : Class S K (C.push σ) τ) (u : WindowCarrier S K C σ) i,
    u.val = .free σ i → Acc (fun t s => RS S K C τ s t) (instanceClass hk v (classOf u)) →
      Acc (fun t s => RS S K (C.push σ) τ s t) v

end LogicLineages.PersistentMarking.NumberedWindowExternalInstancePathTargets
