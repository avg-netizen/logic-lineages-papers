module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus GuardedSource
open GuardedSourceCalibrationProof GuardedSourceRelationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Particular literal wrappers provide the package. Their calibrated inputs
and shared tag/window Programs are chosen before every finite source window. -/
theorem actualUniformTypedSuccessorExists : GuardedSourceTargets.ActualUniformTypedSuccessorExists := by
  intro n arity
  obtain ⟨oldSource,hs⟩ := JointGammaProgramsProof.actualContextUniformPresentationExists n arity
  obtain ⟨oldComp,hc,_,_⟩ := JointGammaComputabilityProof.actualUniformFormulasExist n arity
  obtain ⟨tag,htag⟩ := GuardCalibrationProof.actualTypeTagProgram
  obtain ⟨window,hwindow⟩ := GuardCalibrationProof.actualValidWindowProgram n
  obtain ⟨hs',hc'⟩ := actualGuardedCalibration n arity oldSource oldComp tag window hs hc htag hwindow
  refine ⟨source oldSource oldComp.typed tag window,computability oldComp tag,hs',hc',?_⟩
  intro symbols S table hclosed α typ x y
  have hw : evaluate window
      (List.Vector.ofFn ![OrdinaryArithmeticQuotient.contextCode symbols S table]) = 1 := by
    rw [hwindow]
    exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hclosed
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let P := literalTyped (computability oldComp tag) context typ x ⊓
    literalR (source oldSource oldComp.typed tag window) context x y
  obtain ⟨d⟩ := relationClosure
    (body := SourcePresentation.sourceBody (source oldSource oldComp.typed tag window) context)
    (Gamma := [P]) oldSource oldComp tag window context hw typ x y
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceProof
