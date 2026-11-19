import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperators

namespace LogicLineages.PersistentMarking.NumberedWindowExternalIDStages
open NumberedWindowExternalIDOperators
universe u

/-- An external stage is the operator applied to the union of all
strictly earlier stages, not a natural bound on ordinal depth.
At a point with no predecessor this applies the operator to empty. -/
noncomputable def stage {ι : Type u} (r : ι → ι → Prop) (wf : WellFounded r)
    (F : Operator) : ι → Pred :=
  wf.fix (fun a earlier =>
    F (fun n => ∃ b, ∃ h : r b a, earlier b h n))

end LogicLineages.PersistentMarking.NumberedWindowExternalIDStages
