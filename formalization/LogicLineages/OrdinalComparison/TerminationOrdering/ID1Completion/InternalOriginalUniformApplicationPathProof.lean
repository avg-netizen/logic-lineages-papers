module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPathProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalOriginalUniformApplicationPath InternalOriginalUniformApplicationPathTargets
open InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Both path variants consume the same derived initial invariant. The
existing concrete proofs already discharge the local preservation and edge
compatibility rules, so no source-specific path assumption is introduced. -/
theorem runtimePath (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (oldStep : Program 4) (oldVertex : Program 5)
    (positive : Bool) (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) (hS : SubtypeClosed (fun typ => typ ∈ S))
    (sigma tau : Ty) (parameter gammaCode x y argument certificate out other mapped : OTerm α)
    (h : Nonempty (Derivation body Delta
      (pathPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (normalizeData data) oldStep oldVertex positive sigma tau
        parameter gammaCode x y argument certificate out other mapped))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedPathChecker.checkerGraph
        (InternalParameterizedQuotientEdgeChecker.checker (normalizeData data) oldStep)
        positive InternalOriginalStepGuard.one out other mapped parameter)) := by
  let normalized := normalizeData data
  let ps := parameters sigma tau parameter argument
  have hi := InternalOriginalUniformVertexPathInvariantProof.initialInvariant
    n arity data hc symbols S table hS sigma tau parameter gammaCode argument x (andLeft h)
  have hinput : Nonempty (Derivation body Delta
      (InternalParameterizedApplicationPathLift.inputs
        (InternalParameterizedQuotientEdgeChecker.checker normalized oldStep)
        (InternalOriginalUniformVertexPath.vertex normalized oldVertex)
        (InternalOriginalUniformVertexPath.invariant normalized)
        positive ps x y certificate out other mapped)) := andIntro hi (andRight h)
  cases positive with
  | false =>
    exact InternalOriginalUniformVertexPathProof.actualParameterizedConcreteReflexivePathLift
      body normalized oldStep oldVertex α Delta ps x y certificate out other mapped hinput
  | true =>
    exact InternalOriginalUniformVertexPathProof.actualParameterizedConcretePositivePathLift
      body normalized oldStep oldVertex α Delta ps x y certificate out other mapped hinput

theorem runtimeLaw (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (oldStep : Program 4) (oldVertex : Program 5) (positive : Bool) :
    RuntimePathLaw n (normalizeData data) oldStep oldVertex positive := by
  intro symbols S table hS body α Delta sigma tau parameter gammaCode x y argument certificate out other mapped
  let P := pathPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
    (normalizeData data) oldStep oldVertex positive sigma tau
    parameter gammaCode x y argument certificate out other mapped
  obtain ⟨h⟩ := runtimePath (body := body) (Delta := P :: Delta)
    n arity data hc oldStep oldVertex positive symbols S table hS sigma tau
    parameter gammaCode x y argument certificate out other mapped
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalUniformReflexiveApplicationPath : ActualOriginalUniformReflexiveApplicationPath := by
  intro n arity data hc oldStep oldVertex
  exact runtimeLaw n arity data hc oldStep oldVertex false

theorem actualOriginalUniformPositiveApplicationPath : ActualOriginalUniformPositiveApplicationPath := by
  intro n arity data hc oldStep oldVertex
  exact runtimeLaw n arity data hc oldStep oldVertex true

/-- Calibration of both literal original path functions follows from the
same selected edge. All raw certificate inputs remain quantified. -/
theorem pathCalibration (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4)
    (hc : InternalParameterizedCanonicalQuotientEdgeApplicationLift.SelectedCalibrated
      n arity data oldStep) : PathCalibrated n arity data oldStep := by
  intro symbols S Gamma table hS x y certificate
  have he := (hc symbols S Gamma table hS).1
  exact ⟨InternalParameterizedPathCheckerEvaluationProof.actualOriginalParameterizedPathCheckerEvaluation
      n arity symbols S Gamma table (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
      (InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table) he x y certificate,
    InternalParameterizedPathCheckerEvaluationProof.actualOriginalParameterizedPositivePathCheckerEvaluation
      n arity symbols S Gamma table (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
      (InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table) he x y certificate⟩

theorem actualOriginalUniformApplicationPathSelection : ActualOriginalUniformApplicationPathSelection := by
  intro n arity
  obtain ⟨data,oldStep,hdata,hleaf,hpackage,hcal,_⟩ :=
    InternalParameterizedCanonicalQuotientEdgeApplicationLiftProof.actualOriginalUniformCanonicalQuotientEdgeApplicationSelection
      n arity
  obtain ⟨oldVertex,hvertex,_⟩ :=
    InternalOriginalUniformVertexPathProof.actualOriginalUniformVertexProgram n arity
  exact ⟨data,oldStep,oldVertex,hdata,hleaf,hvertex,hpackage,hcal,
    InternalOriginalUniformVertexPathProof.actualOriginalUniformVertexPathCalibration
      n arity (normalizeData data) oldVertex hpackage.1 hvertex,
    pathCalibration n arity (normalizeData data) oldStep hcal,
    runtimeLaw n arity data hdata oldStep oldVertex false,
    runtimeLaw n arity data hdata oldStep oldVertex true⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPathProof
