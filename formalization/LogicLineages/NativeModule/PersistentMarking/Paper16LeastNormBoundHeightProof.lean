module

public import LogicLineages.NativeModule.PersistentMarking.Paper16LeastNormBoundTargets
import LogicLineages.NativeModule.PersistentMarking.ActualCollapseMainProof
import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformProof
import LogicLineages.NativeModule.PersistentMarking.NativeRankUnconditionalChecks

public section

namespace LogicLineages.PersistentMarking.Paper16LeastNormBoundHeightProof
open ExternalOrdinalInterfaceID1Targets ExternalOrdinalInterfaceTargets
open Paper16RemainingOrdinalTargets Paper16LeastNormBoundTargets
open ConditionalUpperUniformTargets (UniformAccessibility)
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets
open Ordinal

theorem exact_UpperAtLeastNormBound : UpperAtLeastNormBound := by
  intro β hβ uniform
  exact ConditionalUpperUniformProof.exact_ConditionalUpperUniform β hβ.1 uniform

theorem exact_HeightsBetween : HeightsBetween := by
  intro β hβ uniform all A S wfFull wfNative
  have upper := exact_UpperAtLeastNormBound β hβ uniform
  have calibration : Calibration A.collapse :=
    ⟨A.zero, A.successor, A.add, A.mul, A.omega, A.one, A.pow, A.fix, A.arithmetic,
      A.omegaEquations, fun n => all A n⟩
  have tower : ConditionalTowerCofinality.TowerHypotheses A.collapse :=
    ActualCollapse.actualTowerHypotheses A.zero A.successor A.add A.mul A.omega A.one A.pow A.fix
      A.arithmetic A.omegaEquations
  have identify : BHIdentification A.collapse A.endpointValue := rfl
  exact ⟨ConditionalHeightProof.lowerBound A.collapse A.endpointValue calibration tower identify S wfNative,
    ConditionalHeightProof.nativeHeightLe S wfNative wfFull,
    ConditionalHeightProof.heightLeOfUpper β upper.2 S wfFull⟩

theorem exact_EndpointBelowLeastNormBound : EndpointBelowLeastNormBound := by
  intro β hβ uniform all A
  let S : Signature := ⟨[], fun i j name a b h => by simp at h⟩
  obtain ⟨wfNative, wfFull, _⟩ := NativeRankUnconditionalChecks.exact_ActualClosedNativeRanks S indexType
  obtain ⟨low, mid, high⟩ := exact_HeightsBetween β hβ uniform all A S wfFull wfNative
  exact low.trans (mid.trans high)

#print axioms exact_UpperAtLeastNormBound
#print axioms exact_HeightsBetween
#print axioms exact_EndpointBelowLeastNormBound

end LogicLineages.PersistentMarking.Paper16LeastNormBoundHeightProof
