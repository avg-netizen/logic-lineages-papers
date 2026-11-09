module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathPathProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformVertexPath InternalOriginalUniformVertexPathTargets
open InternalOriginalUniformVertexPathSupportProof InternalOriginalUniformVertexPathSyntaxProof
open InternalOriginalUniformVertexPathInvariantProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The original invariant activates both supplied vertex graphs. The
target activation follows through the same quotient edge, then both graphs
expose exactly actualJ with the unchanged RAW argument and parameter. -/
theorem edgeCompatibilityAtArrow (data : Data) (oldStep : Program 4) (oldVertex : Program 5)
    (p d e a x y certificate out other lifted arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hi : Nonempty (Derivation body Gamma (invariantAccepted data p d e a x)))
    (he : Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate p)))
    (hx : Nonempty (Derivation body Gamma (vertexGraph data oldVertex out p d e a x)))
    (hy : Nonempty (Derivation body Gamma (vertexGraph data oldVertex other p d e a y)))
    (hlift : Nonempty (Derivation body Gamma (graph4 edgeLift lifted d e a certificate))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.accepted data oldStep out other lifted p)) := by
  have hf := invariantRecover data p d e a x arrow har hi
  have hiy := invariantPreserveAtArrow data oldStep p d e a x y certificate arrow har hi he
  have hjx := vertexRecover data oldVertex p d e a x out (invariantActivation data p d e a x hi) hx
  have hjy := vertexRecover data oldVertex p d e a y other (invariantActivation data p d e a y hiy) hy
  exact InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof.applicationLift
    data oldStep arrow d e x y a certificate out other lifted p
    (andIntro (andIntro har (andRight hf))
      (andIntro (andLeft (andLeft hf))
        (andIntro (andRight (andLeft hf)) (andIntro he (andIntro hjx hjy))))) hlift

/-- The original cons constructor is total in the original calculus. Its
arrow witness is eliminated while all supplied vertex and edge outputs stay. -/
theorem edgeCompatibility (data : Data) (oldStep : Program 4) (oldVertex : Program 5)
    (p d e a x y certificate out other lifted : OTerm α)
    (hi : Nonempty (Derivation body Gamma (invariantAccepted data p d e a x)))
    (he : Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate p)))
    (hx : Nonempty (Derivation body Gamma (vertexGraph data oldVertex out p d e a x)))
    (hy : Nonempty (Derivation body Gamma (vertexGraph data oldVertex other p d e a y)))
    (hlift : Nonempty (Derivation body Gamma (graph4 edgeLift lifted d e a certificate))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.accepted data oldStep out other lifted p)) := by
  apply programCases InternalListCodec.consCode (Fin.cons d (Fin.cons e Fin.elim0)) _
  intro β j Delta arrow hj har
  rw [edgeAcceptedRename]
  have hi' := renameInto hi j Delta hj
  have he' := renameInto he j Delta hj
  have hx' := renameInto hx j Delta hj
  have hy' := renameInto hy j Delta hj
  have hlift' := renameInto hlift j Delta hj
  rw [invariantRename] at hi'
  rw [edgeAcceptedRename] at he'
  rw [vertexRename] at hx' hy'
  rw [graph4Rename] at hlift'
  simp only [consTermRename,emptyRename] at har
  exact edgeCompatibilityAtArrow data oldStep oldVertex
    (p.relabel j) (d.relabel j) (e.relabel j) (a.relabel j) (x.relabel j) (y.relabel j)
    (certificate.relabel j) (out.relabel j) (other.relabel j) (lifted.relabel j)
    arrow har hi' he' hx' hy' hlift'

theorem actualParameterizedVertexEdgeCompatibility : ActualParameterizedVertexEdgeCompatibility := by
  intro body data oldStep oldVertex α ps x y certificate out other lifted
  let P := invariantAccepted data (ps 0) (ps 1) (ps 2) (ps 3) x ⊓
    (InternalParameterizedQuotientEdgeChecker.accepted data oldStep x y certificate (ps 0) ⊓
      (vertexGraph data oldVertex out (ps 0) (ps 1) (ps 2) (ps 3) x ⊓
        (vertexGraph data oldVertex other (ps 0) (ps 1) (ps 2) (ps 3) y ⊓
          graph4 edgeLift lifted (ps 1) (ps 2) (ps 3) certificate)))
  have h : Nonempty (Derivation body [P] P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hp⟩ := edgeCompatibility (body := body) (Gamma := [P]) data oldStep oldVertex
    (ps 0) (ps 1) (ps 2) (ps 3) x y certificate out other lifted
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction hp⟩

theorem actualParameterizedConcreteReflexivePathLift : ActualParameterizedConcreteReflexivePathLift := by
  intro body data oldStep oldVertex α Delta ps x y code out other mapped hi
  exact InternalParameterizedApplicationPathLiftProof.actualInternalParameterizedReflexivePathLift
    body (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
    (vertex data oldVertex) (invariant data)
    (actualParameterizedVertexInvariantPreservation body data oldStep)
    (actualParameterizedVertexEdgeCompatibility body data oldStep oldVertex)
    α Delta ps x y code out other mapped hi

theorem actualParameterizedConcretePositivePathLift : ActualParameterizedConcretePositivePathLift := by
  intro body data oldStep oldVertex α Delta ps x y code out other mapped hi
  exact InternalParameterizedApplicationPathLiftProof.actualInternalParameterizedPositivePathLift
    body (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
    (vertex data oldVertex) (invariant data)
    (actualParameterizedVertexInvariantPreservation body data oldStep)
    (actualParameterizedVertexEdgeCompatibility body data oldStep oldVertex)
    α Delta ps x y code out other mapped hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathPathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathPathProof
