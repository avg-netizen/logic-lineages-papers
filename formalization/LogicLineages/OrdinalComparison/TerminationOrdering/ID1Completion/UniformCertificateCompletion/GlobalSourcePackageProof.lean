module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
open GlobalSourcePackage

/-- Every witness is selected jointly in the original runtime context.
No finite source window or ambient Gamma has been introduced yet. -/
theorem actualOriginalGlobalInputSelection :
    GlobalSourcePackageTargets.ActualOriginalGlobalInputSelection := by
  intro n arity
  obtain ⟨base,hbase,_,_⟩ :=
    InternalOriginalUniformDescentSelectionProof.actualOriginalUniformDescentSelection n arity
  obtain ⟨window,hwindow⟩ := GuardCalibrationProof.actualValidWindowProgram n
  obtain ⟨oldSrc,hsrc⟩ := JointGammaProgramsProof.actualContextUniformPresentationExists n arity
  obtain ⟨oldComp,hcomp,_,_⟩ := JointGammaComputabilityProof.actualUniformFormulasExist n arity
  obtain ⟨oldStep,hstep,_⟩ :=
    InternalOriginalUniformApplicationStepSelectionProof.actualOriginalUniformStepLeafProgram n arity
  obtain ⟨oldVertex,hvertex,_⟩ := RuntimeVertexProof.actualGlobalRuntimeVertexSelection n arity
  obtain ⟨oldResult,_,hresult,_,_⟩ := ApplicationResultBuilderProof.actualProgramWitnesses n arity
  exact ⟨⟨base,window,oldSrc,oldComp,oldStep,oldVertex,oldResult⟩,
    hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩

/-- Native calibration and the internal certificate theorem have separate
proved suppliers, applied to the SAME literal constructors. Full Option
success is retained independently of the total defaulted result equality. -/
theorem actualOriginalGlobalSourcePackageConstruction :
    GlobalSourcePackageTargets.ActualOriginalGlobalSourcePackageConstruction := by
  intro n arity p hp
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  have hr := OuterResultCalibrationProof.actualOriginalOuterResultComputabilityCalibration
    n arity p.base p.window p.oldComp p.oldVertex p.oldResult
    hbase hwindow hcomp hvertex hresult
  refine ⟨hr.result,?_,?_⟩
  · intro v hactive
    exact OuterResultCalibrationProof.actualOriginalOuterActiveResultSuccess
      n arity p.base p.window p.oldComp p.oldVertex p.oldResult
      hbase hwindow hcomp hvertex v hactive
  · refine ⟨?_,hr.computability,?_,?_⟩
    · exact OuterSourceCalibrationProof.actualOriginalOuterSourceCalibration
        n arity p.base p.window p.oldSrc p.oldComp p.oldStep
        hbase hwindow hsrc hcomp hstep
    · exact OuterSourceCalibrationProof.actualOriginalOuterObjectLiftCalibration
        n arity p.base p.window p.oldVertex hbase hwindow hvertex
    · exact OuterProof.actualConcreteUniformCertificateDownwardPackage
        n arity p.base hbase p.window hwindow p.oldSrc p.oldComp p.oldStep p.oldVertex p.oldResult

/-- ONE final source/comp/lift is selected before all finite windows.
The unqualified internal lift remains a proved conclusion of the package. -/
theorem actualOriginalGlobalSourceDownwardPackageExists :
    GlobalSourcePackageTargets.ActualOriginalGlobalSourceDownwardPackageExists := by
  intro n arity
  obtain ⟨p,hp⟩ := actualOriginalGlobalInputSelection n arity
  exact ⟨source p,computability p,lift p,
    (actualOriginalGlobalSourcePackageConstruction n arity p hp).2.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
