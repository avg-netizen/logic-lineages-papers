module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyCalibrationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly

/-- Every preserved leaf is a literal projection of the same selection. -/
theorem actualOriginalObjectAssemblyPreservedLeaves :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualOriginalObjectAssemblyPreservedLeaves := by
  intro K Gamma p
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Patch just the three selected dispatch leaves, retaining all other global
calibrations and using the same canonical data throughout. -/
theorem actualOriginalObjectAssemblyPatchedCalibration :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualOriginalObjectAssemblyPatchedCalibration := by
  intro n arity symbols S Gamma table p hc hi
  obtain ⟨hd,hs,ht,hr,hv,hl,hw⟩ := hi
  refine ⟨?_,?_,?_⟩
  · exact ⟨hs.1,hs.2.1,
      InternalOriginalObjectFiberSourceDispatchProof.actualOriginalObjectSourcePositiveCalibration
        n arity symbols S Gamma table p.canonical p.oldSource.positive hc hd hs.2.2.1,
      hs.2.2.2⟩
  · exact ⟨InternalOriginalObjectFiberSourceDispatchProof.actualOriginalObjectSourceTypedCalibration
      n arity symbols S Gamma table p.canonical p.oldComp.typed hc hd ht.1,ht.2⟩
  · exact InternalOriginalObjectFiberSourceDispatchProof.actualOriginalObjectSourceResultCalibration
      n arity symbols S Gamma table p.canonical p.oldResult hc hd hr

/-- Normalize the actual patched records and calibrate the actual path package.
All suppliers are universal at this selection; no new witness is selected. -/
theorem actualOriginalObjectAssemblyCalibration :
    InternalOriginalObjectFiberSourceAssemblyTargets.ActualOriginalObjectAssemblyCalibration := by
  intro n arity symbols S Gamma table p hc hi
  obtain ⟨hps,hpc,hpr⟩ :=
    actualOriginalObjectAssemblyPatchedCalibration n arity symbols S Gamma table p hc hi
  obtain ⟨hd,hs,ht,hr,hv,hl,hw⟩ := hi
  obtain ⟨hgamma,hvalid,htag,harrow⟩ :=
    InternalOriginalObjectFiberSourceDispatchProof.actualOriginalObjectSourceAuxiliaryCalibration
  let K := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hb := GammaGuardedSourceCalibrationProof.actualBaseCalibration n arity
    (patchedSource K Gamma p) (patchedComp K Gamma p)
    InternalOriginalObjectFiberSourceDispatch.valid
    InternalOriginalObjectFiberSourceDispatch.gamma hps hpc hvalid hgamma
  have hg := GuardedSourceCalibrationProof.actualGuardedCalibration n arity
    (GammaGuardedSource.baseSource (patchedSource K Gamma p)
      InternalOriginalObjectFiberSourceDispatch.gamma)
    (GammaGuardedSource.baseComputability (patchedComp K Gamma p)
      InternalOriginalObjectFiberSourceDispatch.valid
      InternalOriginalObjectFiberSourceDispatch.gamma)
    InternalOriginalObjectFiberSourceDispatch.tag p.window hb.1 hb.2 htag hw
  have hsrc : ContextUniform.Calibrated (src K Gamma p) n arity := hg.1
  have hbase : JointGammaComputability.Calibrated (baseComp K Gamma p) n arity := hg.2
  have happ : JointGammaComputability.Calibrated (comp K Gamma p) n arity :=
    InternalApplicationCalibrationProof.actualCalibration n arity (baseComp K Gamma p)
      p.window InternalOriginalObjectFiberSourceDispatch.arrow (patchedResult K Gamma p)
      hbase hw harrow hpr
  refine ⟨hsrc,hbase,happ,hpr,?_,?_,?_,?_⟩
  · exact InternalCanonicalFixedWindowVertexDispatchProof.actualOriginalCanonicalFixedWindowVertexCalibration
      n arity symbols S Gamma table p.canonical p.oldVertex hc hd hv
  · exact InternalCanonicalFixedWindowPathLiftProof.actualOriginalCanonicalFixedWindowLiftPathCalibration
      n arity symbols S Gamma table p.canonical p.oldVertex hc hd hv
  · exact InternalCanonicalFixedWindowPathLiftProof.actualOriginalCanonicalFixedWindowDecodedPathValue
      n arity symbols S Gamma table p.canonical p.oldVertex hc hd hv
  · exact InternalOriginalObjectFiberPathDispatchProof.actualOriginalObjectFiberPathValueCalibration
      n arity symbols S Gamma table p.canonical p.oldVertex p.oldLift hc hd hv hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyCalibrationProof
