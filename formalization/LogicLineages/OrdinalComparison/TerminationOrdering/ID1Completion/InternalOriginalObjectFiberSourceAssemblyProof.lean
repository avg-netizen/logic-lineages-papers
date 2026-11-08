module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyProof
open Source InternalOriginalObjectFiberSourceAssembly
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalObjectAssemblyPreservedLeaves :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualOriginalObjectAssemblyPreservedLeaves :=
  InternalOriginalObjectFiberSourceAssemblyCalibrationProof.actualOriginalObjectAssemblyPreservedLeaves

theorem actualOriginalObjectAssemblyPatchedCalibration :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualOriginalObjectAssemblyPatchedCalibration :=
  InternalOriginalObjectFiberSourceAssemblyCalibrationProof.actualOriginalObjectAssemblyPatchedCalibration

theorem actualOriginalObjectAssemblyCalibration :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualOriginalObjectAssemblyCalibration :=
  InternalOriginalObjectFiberSourceAssemblyCalibrationProof.actualOriginalObjectAssemblyCalibration

theorem actualInternalOriginalObjectAssemblyTypedClosure :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualInternalOriginalObjectAssemblyTypedClosure :=
  InternalOriginalObjectFiberSourceAssemblyClosureProof.actualInternalOriginalObjectAssemblyTypedClosure

theorem actualInternalOriginalObjectAssemblyGroundClosure :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualInternalOriginalObjectAssemblyGroundClosure :=
  InternalOriginalObjectFiberSourceAssemblyClosureProof.actualInternalOriginalObjectAssemblyGroundClosure

theorem actualInternalOriginalObjectAssemblyGuardTransport :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualInternalOriginalObjectAssemblyGuardTransport :=
  InternalOriginalObjectFiberSourceAssemblyClosureProof.actualInternalOriginalObjectAssemblyGuardTransport

theorem actualInternalOriginalObjectAssemblyApplicationTotality :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualInternalOriginalObjectAssemblyApplicationTotality :=
  InternalOriginalObjectFiberSourceAssemblyClosureProof.actualInternalOriginalObjectAssemblyApplicationTotality

theorem actualInternalOriginalObjectAssemblyApplicationFunctionality :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualInternalOriginalObjectAssemblyApplicationFunctionality :=
  InternalOriginalObjectFiberSourceAssemblyClosureProof.actualInternalOriginalObjectAssemblyApplicationFunctionality

theorem actualInternalOriginalObjectAssemblyApplicationComputability :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualInternalOriginalObjectAssemblyApplicationComputability :=
  InternalOriginalObjectFiberSourceAssemblyClosureProof.actualInternalOriginalObjectAssemblyApplicationComputability

theorem actualInternalOriginalObjectAssemblyResultComputability :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualInternalOriginalObjectAssemblyResultComputability :=
  InternalOriginalObjectFiberSourceAssemblyClosureProof.actualInternalOriginalObjectAssemblyResultComputability

/-- Select the path package ONCE. Only independent globally calibrated old
leaves are then selected; all source dispatch and closure laws specialize to
that same canonical Data and those same assembled Programs. -/
theorem actualOriginalSelectedObjectFiberSourceAssembly :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualOriginalSelectedObjectFiberSourceAssembly := by
  intro n arity symbols S Gamma table hc
  obtain ⟨data,oldVertex,oldLift,hd,hs,happ,he,hal,ho,hv,hp,hdec,hvL,hi,hpL,hold,hl,hlL⟩ :=
    InternalOriginalObjectFiberPathDispatchProof.actualOriginalSelectedObjectFiberPathDispatch
      n arity symbols S Gamma table hc
  obtain ⟨oldSource,hsource⟩ := JointGammaProgramsProof.actualContextUniformPresentationExists n arity
  obtain ⟨oldComp,hcomp,_,_⟩ := JointGammaComputabilityProof.actualUniformFormulasExist n arity
  obtain ⟨oldResult,success,hresult,_,_⟩ := ApplicationResultBuilderProof.actualProgramWitnesses n arity
  obtain ⟨window,hwindow⟩ := GuardCalibrationProof.actualValidWindowProgram n
  let K := OrdinaryArithmeticQuotient.contextCode symbols S table
  let p : Selection := {
    canonical := data
    oldSource := oldSource
    oldComp := oldComp
    oldResult := oldResult
    oldVertex := oldVertex
    oldLift := oldLift
    window := window }
  have hin : InputsCalibrated n arity symbols S Gamma table p :=
    ⟨hd,hsource,hcomp,hresult,ho,hold,hwindow⟩
  refine ⟨p,hin,hs,happ,
    actualOriginalObjectAssemblyPatchedCalibration n arity symbols S Gamma table p hc hin,
    actualOriginalObjectAssemblyCalibration n arity symbols S Gamma table p hc hin,?_,?_⟩
  · refine ⟨he,hal,?_,hvL,hi,hpL,hlL⟩
    exact ⟨InternalOriginalObjectFiberSourceDispatchProof.actualInternalOriginalObjectSourcePositiveGraph
        K Gamma data oldSource.positive,
      InternalOriginalObjectFiberSourceDispatchProof.actualInternalOriginalObjectSourceTypedGraph
        K Gamma data oldComp.typed,
      InternalOriginalObjectFiberSourceDispatchProof.actualInternalOriginalObjectSourceResultGraph
        K Gamma data oldResult,
      InternalOriginalObjectFiberSourceDispatchProof.actualInternalOriginalObjectSourcePositiveZeroGraph
        K Gamma data oldSource.positive,
      InternalOriginalObjectFiberSourceDispatchProof.actualInternalOriginalObjectSourceTypedZeroGraph
        K Gamma data oldComp.typed,
      InternalOriginalObjectFiberSourceDispatchProof.actualInternalOriginalObjectSourceResultZeroGraph
        K Gamma data oldResult⟩
  · constructor
    · intro sourceSymbols sourceTypes sourceTable hclosed
      let context := OrdinaryArithmeticQuotient.contextCode sourceSymbols sourceTypes sourceTable
      have hw : evaluate p.window (List.Vector.ofFn ![context]) = 1 := by
        change evaluate window (List.Vector.ofFn ![context]) = 1
        rw [hwindow]
        exact (GuardCalibrationProof.actualOriginalWindowCalibration
          n sourceSymbols sourceTypes sourceTable).mpr hclosed
      exact ⟨actualInternalOriginalObjectAssemblyTypedClosure K Gamma p context hw,
        actualInternalOriginalObjectAssemblyGroundClosure K Gamma p context hw,
        actualInternalOriginalObjectAssemblyApplicationTotality K Gamma p context hw,
        actualInternalOriginalObjectAssemblyApplicationFunctionality K Gamma p context hw,
        actualInternalOriginalObjectAssemblyApplicationComputability K Gamma p context hw,
        actualInternalOriginalObjectAssemblyResultComputability K Gamma p context hw⟩
    · intro context
      exact actualInternalOriginalObjectAssemblyGuardTransport K Gamma p context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyProof
