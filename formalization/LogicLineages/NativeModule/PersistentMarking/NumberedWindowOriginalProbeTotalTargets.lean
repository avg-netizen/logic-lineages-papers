module

public import LogicLineages.PersistentMarking.NumberedWindowProbeCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalComputabilityFormulaTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTypedProbeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalProbeTotalTargets
open NumberedWindowProbeCode (code NumericalTotal)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open NumberedWindowArithmeticTyCode (encodeTy)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowAddressApplication (graph)
def ExactFormulaTypeCoding := ∀ τ : Ty, code (formulaType τ) = encodeTy τ
def OriginalProbeTotal := ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
  NumericalTotal (typed (fixed S K)) (probe (fixed S K)) (graph (fixed S K))
end LogicLineages.PersistentMarking.NumberedWindowOriginalProbeTotalTargets
