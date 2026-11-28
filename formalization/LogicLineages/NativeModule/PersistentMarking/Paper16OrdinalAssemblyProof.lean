module

public import LogicLineages.NativeModule.PersistentMarking.Paper16OrdinalAssemblyTargets
import LogicLineages.NativeModule.PersistentMarking.ActualCollapseMainProof
import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformProof

public section

namespace LogicLineages.PersistentMarking.Paper16OrdinalAssemblyProof
open Ordinal ActualCollapse ConditionalTowerCofinality
open Paper16RemainingOrdinalTargets ExternalOrdinalInterfaceTargets Paper16OrdinalAssemblyTargets
open ConditionalUpperUniformTargets (UniformAccessibility)

theorem exact_OrdinalSemanticsExistence : OrdinalSemanticsExistence := by
  obtain ⟨Z, s, add, mul, w, one, pow, fix, h1, h2⟩ := ActualCollapseMain.solutionExists
  exact ⟨⟨Z, s, add, mul, w, one, pow, fix, h1, h2⟩⟩

theorem exact_CofinalityAtActualEndpoint : CofinalityAtActualEndpoint := by
  intro A
  exact (ActualCollapseMain.actualTowerCofinality A.zero A.successor A.add A.mul A.omega A.one A.pow
    A.fix A.arithmetic A.omegaEquations).1

theorem exact_EndpointSelfIdentification : EndpointSelfIdentification := by
  intro A
  exact rfl

theorem exact_CalibrationFromPointwise : CalibrationFromPointwise := by
  intro all A
  exact ⟨A.zero, A.successor, A.add, A.mul, A.omega, A.one, A.pow, A.fix, A.arithmetic,
    A.omegaEquations, fun n => all A n⟩

theorem exact_UpperFromInputs : UpperFromInputs := by
  intro norm uniform A
  exact ConditionalUpperUniformProof.exact_ConditionalUpperUniform A.endpointValue (norm A) uniform

theorem exact_UpperAtCitedFromAccessibility : UpperAtCitedFromAccessibility := by
  intro citedBH uniform norm
  exact ConditionalUpperUniformProof.exact_ConditionalUpperUniform citedBH norm uniform

theorem exact_CitedCofinalityFromIdentification : CitedCofinalityFromIdentification := by
  intro citedBH identify A
  exact ⟨exact_CofinalityAtActualEndpoint A, identify A⟩

theorem exact_HeightFromInputs : HeightFromInputs := by
  intro norm uniform all A
  exact ActualCollapseMain.actualHeightEffective A.zero A.successor A.add A.mul A.omega A.one A.pow
    A.fix A.arithmetic A.omegaEquations A.endpointValue (exact_CalibrationFromPointwise all A)
    (exact_EndpointSelfIdentification A) (exact_UpperFromInputs norm uniform A).2

theorem exact_PrincipalFromInputs : PrincipalFromInputs := by
  intro norm uniform all A
  exact ActualCollapseMain.actualMain16 A.zero A.successor A.add A.mul A.omega A.one A.pow
    A.fix A.arithmetic A.omegaEquations A.endpointValue (norm A) uniform
    (exact_CalibrationFromPointwise all A) (exact_EndpointSelfIdentification A)

theorem exact_PrintedFromInputs : PrintedFromInputs := by
  intro citedBH norm uniform all identify
  obtain ⟨A⟩ := exact_OrdinalSemanticsExistence
  have upper : ConditionalUpperTargets.UpperStatement citedBH :=
    ConditionalUpperUniformProof.exact_ConditionalUpperUniform citedBH norm uniform
  refine ⟨upper, fun A' => (exact_CofinalityAtActualEndpoint A').trans (identify A'), ?_, ?_⟩
  · exact ActualCollapseMain.actualHeightEffective A.zero A.successor A.add A.mul A.omega A.one A.pow
      A.fix A.arithmetic A.omegaEquations citedBH (exact_CalibrationFromPointwise all A)
      (identify A) upper.2
  · exact ActualCollapseMain.actualMain16 A.zero A.successor A.add A.mul A.omega A.one A.pow
      A.fix A.arithmetic A.omegaEquations citedBH norm uniform
      (exact_CalibrationFromPointwise all A) (identify A)

#print axioms exact_OrdinalSemanticsExistence
#print axioms exact_CofinalityAtActualEndpoint
#print axioms exact_EndpointSelfIdentification
#print axioms exact_CalibrationFromPointwise
#print axioms exact_UpperFromInputs
#print axioms exact_UpperAtCitedFromAccessibility
#print axioms exact_CitedCofinalityFromIdentification
#print axioms exact_HeightFromInputs
#print axioms exact_PrincipalFromInputs
#print axioms exact_PrintedFromInputs

end LogicLineages.PersistentMarking.Paper16OrdinalAssemblyProof
