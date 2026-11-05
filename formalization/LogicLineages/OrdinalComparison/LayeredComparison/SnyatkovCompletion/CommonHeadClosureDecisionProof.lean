module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceDecisionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionSemanticInterface
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionCodeInterface

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionProof
open CommonLayerSyntax CommonHeadClosureDecision

theorem actualCodedClosures : CommonHeadClosureDecisionTargets.ActualCodedClosures := by
  intro Γ hg E F desired b
  have h := BaseBooleanSourceProof.actualClosureDecisions
    (CommonLayerComparison.compile (headCodes Γ) E F desired) b
  have he := exists_congr (fun ν => CommonHeadClosureDecisionSuppliers.codedComparison Γ hg E F desired ν)
  have ha := forall_congr' (fun ν => CommonHeadClosureDecisionSuppliers.codedComparison Γ hg E F desired ν)
  rw [he, ha] at h
  exact h

theorem actualSourceClosures : CommonHeadClosureDecisionTargets.ActualSourceClosures := by
  intro Γ hg E F desired b
  have h := actualCodedClosures Γ hg (encodeCommon Γ.length E) (encodeCommon Γ.length F) desired b
  simpa only [CommonHeadClosureDecisionSuppliers.sourceCalibration Γ E,
    CommonHeadClosureDecisionSuppliers.sourceCalibration Γ F] using h

private theorem exists_domain (p : BaseFormula.Formula) :
    (BaseBooleanSource.Code.decideClosureExists p.encode).isSome = true := by
  rw [BaseBooleanSource.Code.decideClosureExists, BaseBooleanSourceProof.literalCompiler,
    SourceBooleanProgramsProof.decideExists_calibration]
  simp only [SourceBooleanGraph.decideExists, if_pos (BaseBooleanSourceProof.exactSourceData p).1,
    Option.isSome_some]

private theorem forall_domain (p : BaseFormula.Formula) :
    (BaseBooleanSource.Code.decideClosureForall p.encode).isSome = true := by
  rw [BaseBooleanSource.Code.decideClosureForall, BaseBooleanSourceProof.literalCompiler,
    SourceBooleanProgramsProof.decideForall_calibration]
  simp only [SourceBooleanGraph.decideForall, Option.isSome_map, SourceBooleanGraph.decideExists,
    SourceBooleanGraph.test, if_pos (BaseBooleanSourceProof.exactSourceData p).1, Option.isSome_some]

theorem unconditionalDecisionDomain : CommonHeadClosureDecisionTargets.UnconditionalDecisionDomain :=
  fun p => ⟨exists_domain (CommonLayerComparison.compile p.1 p.2.1 p.2.2.1 p.2.2.2),
    forall_domain (CommonLayerComparison.compile p.1 p.2.1 p.2.2.1 p.2.2.2)⟩

theorem actualAllCodePrograms : CommonHeadClosureDecisionTargets.ActualAllCodePrograms :=
  ⟨BaseBooleanSourceProof.decideClosureExists_primitive.to_comp.comp CommonHeadClosureDecisionSuppliers.allCodeEffectivity,
    BaseBooleanSourceProof.decideClosureForall_primitive.to_comp.comp CommonHeadClosureDecisionSuppliers.allCodeEffectivity⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionProof
