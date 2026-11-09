module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathInvariantProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformVertexPath InternalOriginalUniformVertexPathTargets
open InternalOriginalUniformVertexPathSupportProof InternalOriginalUniformVertexPathSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- At an actual symbolic arrow, only function typing moves. The argument
typing and codomain membership stay at their identical parameter coordinates. -/
theorem invariantPreserveAtArrow (data : Data) (oldStep : Program 4)
    (p d e a x y certificate arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hi : Nonempty (Derivation body Gamma (invariantAccepted data p d e a x)))
    (he : Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate p))) :
    Nonempty (Derivation body Gamma (invariantAccepted data p d e a y)) := by
  have hf := invariantRecover data p d e a x arrow har hi
  have hy := InternalParameterizedQuotientEdgeCheckerTypedProof.typedPropagation
    data oldStep x y certificate arrow p (andLeft (andLeft hf)) he
  exact invariantAccept data p d e a y arrow har
    (andIntro (andIntro hy (andRight (andLeft hf))) (andRight hf))

/-- The original total cons constructor binds the arrow internally. It is
not an extra invariant or calibration assumption of the propagation rule. -/
theorem invariantPreserve (data : Data) (oldStep : Program 4)
    (p d e a x y certificate : OTerm α)
    (hi : Nonempty (Derivation body Gamma (invariantAccepted data p d e a x)))
    (he : Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate p))) :
    Nonempty (Derivation body Gamma (invariantAccepted data p d e a y)) := by
  apply programCases InternalListCodec.consCode (Fin.cons d (Fin.cons e Fin.elim0)) _
  intro β j Delta arrow hj har
  rw [invariantRename]
  have hi' := renameInto hi j Delta hj
  have he' := renameInto he j Delta hj
  rw [invariantRename] at hi'
  rw [edgeAcceptedRename] at he'
  simp only [consTermRename,emptyRename] at har
  exact invariantPreserveAtArrow data oldStep (p.relabel j) (d.relabel j) (e.relabel j)
    (a.relabel j) (x.relabel j) (y.relabel j) (certificate.relabel j) arrow har hi' he'

theorem actualParameterizedVertexInvariantPreservation :
    ActualParameterizedVertexInvariantPreservation := by
  intro body data oldStep α ps x y certificate
  let P := invariantAccepted data (ps 0) (ps 1) (ps 2) (ps 3) x ⊓
    InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate (ps 0)
  have h : Nonempty (Derivation body [P] P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hp⟩ := invariantPreserve (body := body) (Gamma := [P]) data oldStep
    (ps 0) (ps 1) (ps 2) (ps 3) x y certificate (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hp⟩

/-- Only closed source type/context computation is imported. The literal
pair graph and actual selected typing remain the internal symbolic premises. -/
theorem initialInvariant (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (parameter gammaCode argument value : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (initialPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (InternalOriginalUniformContextMembership.normalizeData data) sigma tau
        parameter gammaCode argument value))) :
    Nonempty (Derivation body Gamma
      (invariantAccepted (InternalOriginalUniformContextMembership.normalizeData data)
        parameter (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument value)) := by
  let normalized := InternalOriginalUniformContextMembership.normalizeData data
  have hf := andLeft (andRight h)
  have ha := andRight (andRight h)
  have hmArrow := andLeft (InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    normalized.oldRepresentative (InternalOriginalUniformDescentSelection.validity normalized)
    normalized.member value (numeral (typeNumber (.arrow sigma tau))) parameter hf)
  have hm := InternalOriginalUniformApplicationTypingMembershipProof.codomainMembership
    n arity data hc symbols S table hS sigma tau parameter gammaCode (andLeft h) hmArrow
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral
    (body := body) (Gamma := Gamma) (α := α) sigma tau
  exact invariantAccept normalized parameter (numeral (typeNumber sigma))
    (numeral (typeNumber tau)) argument value (numeral (typeNumber (.arrow sigma tau))) har
    (andIntro (andIntro hf ha) hm)

theorem actualOriginalUniformInitialVertexInvariant : ActualOriginalUniformInitialVertexInvariant := by
  intro n arity data hc symbols S table hS body α Delta sigma tau p gammaCode a x
  let P := initialPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
    (InternalOriginalUniformContextMembership.normalizeData data) sigma tau p gammaCode a x
  obtain ⟨h⟩ := initialInvariant (body := body) (Gamma := P :: Delta)
    n arity data hc symbols S table hS sigma tau p gammaCode a x
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathInvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathInvariantProof
