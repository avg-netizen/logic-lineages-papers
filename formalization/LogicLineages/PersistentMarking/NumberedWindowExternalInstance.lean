import LogicLineages.PersistentMarking.NumberedWindowExternalArgumentSubstitutionChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalInstance
open NumberedWindowSimulationData NumberedWindowExternalSubstitutionTargets
open NumberedWindowExternalArgumentSubstitutionChecks

/-- Instantiation on both original typed primary classes. -/
def instanceClass {S K C σ τ} (hk : DecisionSourceUniverse.Closed K)
    (v : Class S K (Spine.BoundContext.push C σ) τ) (u : Class S K C σ) : Class S K C τ :=
  Quot.lift (fun body : WindowCarrier S K (Spine.BoundContext.push C σ) τ =>
    Quot.lift (fun a : WindowCarrier S K C σ => classOf (bodyInstance hk body a))
      (fun a b h => exact_LiteralInstanceClassSubstitution S K C σ τ hk body body a b
        rfl (Quot.sound h)) u)
    (fun body other p => Quot.inductionOn u (fun a =>
      exact_LiteralInstanceClassSubstitution S K C σ τ hk body other a a
        (Quot.sound p) rfl)) v

end LogicLineages.PersistentMarking.NumberedWindowExternalInstance
