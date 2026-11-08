module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalCanonicalFixedWindowVertexDispatch InternalApplicationCertificateConstructors
open InternalCanonicalFixedWindowVertexDispatchSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalCanonicalFixedWindowActiveVertexEquality :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualOriginalCanonicalFixedWindowActiveVertexEquality :=
  InternalCanonicalFixedWindowVertexDispatchEvaluationProof.actualOriginalCanonicalFixedWindowActiveVertexEquality

theorem actualOriginalCanonicalFixedWindowVertexCalibration :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualOriginalCanonicalFixedWindowVertexCalibration :=
  InternalCanonicalFixedWindowVertexDispatchEvaluationProof.actualOriginalCanonicalFixedWindowVertexCalibration

theorem actualInternalCanonicalFixedWindowVertexActivation :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowVertexActivation := by
  intro window data body α Delta context domain codomain argument value arrow
  let a := graph2 InternalListCodec.consCode arrow domain codomain
  let g := activationAccepted window data context domain codomain argument value
  let f := activationFactors window data context domain argument value arrow
  obtain ⟨hf⟩ := activationRecover (body := body) (Gamma := g :: a :: Delta)
    window data context domain codomain argument value arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := activationAccept (body := body) (Gamma := f :: a :: Delta)
    window data context domain codomain argument value arrow
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualInternalCanonicalFixedWindowActiveVertexGraph :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowActiveVertexGraph := by
  intro window data oldVertex body α Delta context domain codomain argument value out
  let a := activationAccepted window data context domain codomain argument value
  let g := vertexGraph window data oldVertex out context domain codomain argument value
  let f := applicationGraph data out domain codomain value argument
  obtain ⟨hf⟩ := vertexRecover (body := body) (Gamma := g :: a :: Delta)
    window data oldVertex context domain codomain argument value out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := vertexAccept (body := body) (Gamma := f :: a :: Delta)
    window data oldVertex context domain codomain argument value out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualInternalCanonicalFixedWindowInvariantFactors :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowInvariantFactors :=
  InternalCanonicalFixedWindowVertexDispatchInvariantProof.actualInternalCanonicalFixedWindowInvariantFactors

theorem actualInternalCanonicalFixedWindowInvariantActivation :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowInvariantActivation :=
  InternalCanonicalFixedWindowVertexDispatchInvariantProof.actualInternalCanonicalFixedWindowInvariantActivation

theorem actualInternalCanonicalFixedWindowInvariantPreservation :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualInternalCanonicalFixedWindowInvariantPreservation :=
  InternalCanonicalFixedWindowVertexDispatchInvariantProof.actualInternalCanonicalFixedWindowInvariantPreservation

theorem actualOriginalCanonicalFixedWindowVertexSelection :
    InternalCanonicalFixedWindowVertexDispatchTargets.ActualOriginalCanonicalFixedWindowVertexSelection := by
  intro n arity symbols S Gamma table hc
  obtain ⟨data,hdata,hselected,hedge⟩ :=
    InternalCanonicalQuotientEdgeSelectionProof.actualOriginalCanonicalEdgeSelection
      n arity symbols S Gamma table hc
  obtain ⟨oldVertex,hold⟩ :=
    InternalApplicationPathMapEvaluationProof.actualOriginalVertexProgramExists n arity Gamma
  refine ⟨data,oldVertex,hdata,hselected,hedge,hold,
    actualOriginalCanonicalFixedWindowVertexCalibration
      n arity symbols S Gamma table data oldVertex hc hdata hold,?_,?_⟩
  · intro body α Delta
    exact ⟨fun context domain codomain argument value arrow =>
        actualInternalCanonicalFixedWindowVertexActivation
          (OrdinaryArithmeticQuotient.contextCode symbols S table) data body α Delta
          context domain codomain argument value arrow,
      fun context domain codomain argument value out =>
        actualInternalCanonicalFixedWindowActiveVertexGraph
          (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex body α Delta
          context domain codomain argument value out,
      fun sigma tau context domain codomain argument value =>
        ⟨actualInternalCanonicalFixedWindowInvariantFactors
          (OrdinaryArithmeticQuotient.contextCode symbols S table) data sigma tau body α Delta
          context domain codomain argument value,
        actualInternalCanonicalFixedWindowInvariantActivation
          (OrdinaryArithmeticQuotient.contextCode symbols S table) data sigma tau body α Delta
          context domain codomain argument value⟩⟩
  · intro body sigma tau
    exact actualInternalCanonicalFixedWindowInvariantPreservation
      (OrdinaryArithmeticQuotient.contextCode symbols S table) data body sigma tau

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchProof
