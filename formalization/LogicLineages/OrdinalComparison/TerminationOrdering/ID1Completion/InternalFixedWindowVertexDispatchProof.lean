module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalFixedWindowVertexDispatch InternalApplicationCertificateConstructors
open InternalFixedWindowVertexDispatchSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalFixedWindowActiveVertexEquality :
    InternalFixedWindowVertexDispatchTargets.ActualOriginalFixedWindowActiveVertexEquality :=
  InternalFixedWindowVertexDispatchEvaluationProof.actualOriginalFixedWindowActiveVertexEquality

theorem actualOriginalFixedWindowVertexCalibration :
    InternalFixedWindowVertexDispatchTargets.ActualOriginalFixedWindowVertexCalibration :=
  InternalFixedWindowVertexDispatchEvaluationProof.actualOriginalFixedWindowVertexCalibration

theorem actualInternalFixedWindowVertexActivation :
    InternalFixedWindowVertexDispatchTargets.ActualInternalFixedWindowVertexActivation := by
  intro window data body α context domain codomain argument value arrow
  let a := graph2 InternalListCodec.consCode arrow domain codomain
  let g := activationAccepted window data context domain codomain argument value
  let f := activationFactors window data context domain argument value arrow
  obtain ⟨hf⟩ := activationRecover (body := body) (Gamma := [g,a])
    window data context domain codomain argument value arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := activationAccept (body := body) (Gamma := [f,a])
    window data context domain codomain argument value arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualInternalFixedWindowActiveVertexGraph :
    InternalFixedWindowVertexDispatchTargets.ActualInternalFixedWindowActiveVertexGraph := by
  intro window data oldVertex body α context domain codomain argument value out
  let a := activationAccepted window data context domain codomain argument value
  let g := vertexGraph window data oldVertex out context domain codomain argument value
  let f := combineGraph data out domain codomain value argument
  obtain ⟨hf⟩ := vertexRecover (body := body) (Gamma := [g,a])
    window data oldVertex context domain codomain argument value out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := vertexAccept (body := body) (Gamma := [f,a])
    window data oldVertex context domain codomain argument value out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualOriginalFixedWindowVertexSelection :
    InternalFixedWindowVertexDispatchTargets.ActualOriginalFixedWindowVertexSelection := by
  intro n arity symbols S Gamma table hc
  obtain ⟨data,hdata,hselected,_⟩ :=
    InternalCertifiedSourceGuardSelectionProof.actualOriginalCertifiedSourceGuardSelection
      n arity symbols S Gamma table hc
  obtain ⟨oldVertex,hold⟩ :=
    InternalApplicationPathMapEvaluationProof.actualOriginalVertexProgramExists n arity Gamma
  refine ⟨data,oldVertex,hdata,hselected,hold,
    actualOriginalFixedWindowVertexCalibration
      n arity symbols S Gamma table data oldVertex hc hdata hold,?_⟩
  intro body α
  exact ⟨fun context domain codomain argument value arrow =>
      actualInternalFixedWindowVertexActivation
        (OrdinaryArithmeticQuotient.contextCode symbols S table) data body α
        context domain codomain argument value arrow,
    fun context domain codomain argument value out =>
      actualInternalFixedWindowActiveVertexGraph
        (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex body α
        context domain codomain argument value out⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchProof
