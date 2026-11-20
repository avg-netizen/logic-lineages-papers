module
public import LogicLineages.PersistentMarking.NumberedWindowProbeCode
public import LogicLineages.PersistentMarking.NumberedWindowTypedProbe
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWindowTargets
open NumberedWindowProbeCode (code NumericalTotal)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressApplication (graph)

abbrev ProbeTy := LogicLineages.OrdinalComparison.Source.Ty

/-- Every successful original type test, at every raw t and q, selects a
type in the specified finite window. No successful decode is assumed. -/
def TypeSupport (s : Settings) (W : List ProbeTy) : Prop :=
  ∀ t q, typed s t q = true → ∃ τ ∈ W, t = code τ

def ChildClosed (W : List ProbeTy) : Prop :=
  ∀ (σ τ : ProbeTy), LogicLineages.OrdinalComparison.Source.Ty.arrow σ τ ∈ W → τ ∈ W

/-- Numerical interface only. This will be proved for the exact fixed
source and not used as a rule of the object theory. -/
def ValidWindow (s : Settings) (W : List ProbeTy) : Prop :=
  TypeSupport s W ∧ ChildClosed W ∧ NumericalTotal (typed s) (probe s) (graph s)

def ExactProbeCodeInjective : Prop := Function.Injective code

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWindowTargets
