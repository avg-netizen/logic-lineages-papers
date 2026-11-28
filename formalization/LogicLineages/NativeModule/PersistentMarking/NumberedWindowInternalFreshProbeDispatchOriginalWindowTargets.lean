module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWindowTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalProbeTotalTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
open NumberedWindowInternalFreshProbeDispatchWindowTargets
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)

/-- The unchanged original source type conversion and the unchanged
literal window list, including its order and duplicate entries. -/
def sourceWindow (K : List Ty) : List ProbeTy := K.map formulaType

def ExactOriginalTypeSupport : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), TypeSupport (fixed S K) (sourceWindow K)

def ExactOriginalWindowChild : Prop :=
  ∀ (K : List Ty), DecisionSourceUniverse.Closed K → ChildClosed (sourceWindow K)

def ExactOriginalValidWindow : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ValidWindow (fixed S K) (sourceWindow K)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
