module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathPathCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableQuotientPath OriginalVariableQuotientPathEdgeProof OriginalVariableQuotientPathPathCoreProof
open OriginalVariableRepresentative (selectedData windowGraph)
open InternalParameterizedCanonicalResultFold (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof
open InternalParameterizedApplicationPathLiftSupportProof
open InternalListCodec InternalListCodecSupportProof
open InternalTagArithmeticSyntaxProof (OTerm z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The first original edge reaches the exact same-type bottom. Its
ordinary tail must be an identity, without a new path induction. -/
theorem variablePositiveAtCons (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y code raw tail parameter typeCode : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hv : Nonempty (Derivation body Gamma (variableAccepted x)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail)))
    (hp : Nonempty (Derivation body Gamma
      (positiveGraph (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
        x y code parameter))) :
    Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode y typeCode)) := by
  apply checkerConsFieldsCases
    (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep)) true
    x y code raw tail parameter _ hc hp
  intro β j Delta vertex certificate hj he ht
  rw [graph1Rename]
  have hw' := renameInto hw j Delta hj
  have hv' := renameInto hv j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [variableAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv'
  rw [graph1Rename] at hl'
  have hb := variableEdge data window oldStep (x.relabel j) vertex certificate (parameter.relabel j)
    (typeCode.relabel j) hw' he hv' hl'
  have hwv := BottomDescentStepProof.windowChange window (suc z) (x.relabel j) vertex (parameter.relabel j) hw'
  obtain ⟨hid⟩ := bottomPathIdentity data window oldStep vertex (y.relabel j) (tail.relabel j)
    (parameter.relabel j) hwv (BottomSourceShapeProof.bottomAccept vertex (typeCode.relabel j) hb) ht
  rw [equalEqn] at hid
  exact outputTransport BottomRepresentative.bottomCode vertex (y.relabel j)
    (Fin.cons (typeCode.relabel j) Fin.elim0) ⟨symm hid⟩ hb

theorem variablePositive (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y code parameter typeCode : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hv : Nonempty (Derivation body Gamma (variableAccepted x)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x)))
    (hp : Nonempty (Derivation body Gamma
      (positiveGraph (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
        x y code parameter))) :
    Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode y typeCode)) := by
  apply positiveConsCases (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
    x y code parameter _ hp
  intro β j Delta raw tail hj hc
  rw [graph1Rename]
  have hw' := renameInto hw j Delta hj
  have hv' := renameInto hv j Delta hj
  have hl' := renameInto hl j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [variableAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv'
  rw [graph1Rename] at hl'
  rw [positiveRename] at hp'
  exact variablePositiveAtCons data window oldStep (x.relabel j) (y.relabel j) (code.relabel j)
    raw tail (parameter.relabel j) (typeCode.relabel j) hw' hv' hl' hc hp'

theorem pathConstructorCases (data : Data) (window : Program 1) (oldStep : Program 4) :
    PathConstructorCases (selectedData data window) (OriginalConstructorLeaf.refined oldStep) window := by
  intro body α Delta x y pathCode parameter typeCode
  refine ⟨?_,?_,?_⟩
  · let A := windowGraph window x parameter ⊓
      (variableAccepted x ⊓ (graph1 InternalUnpair.left typeCode x ⊓
        positiveGraph (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep))
          x y pathCode parameter))
    have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hr⟩ := variablePositive data window oldStep x y pathCode parameter typeCode
      (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
    exact ⟨Derivation.implicationIntroduction hr⟩
  · let A := windowGraph window x parameter ⊓
      (bottomAccepted x ⊓ pathGraph
        (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep)) x y pathCode parameter)
    have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hr⟩ := bottomPathIdentity data window oldStep x y pathCode parameter
      (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
    exact ⟨Derivation.implicationIntroduction hr⟩
  · let A := windowGraph window x parameter ⊓ bottomAccepted x
    let E := positiveGraph
      (edgeChecker (selectedData data window) (OriginalConstructorLeaf.refined oldStep)) x y pathCode parameter
    have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hr⟩ := bottomPositiveContradiction data window oldStep x y pathCode parameter
      (withHyp (andLeft h) E) (withHyp (andRight h) E)
      (show Nonempty (Derivation body (E :: A :: Delta) E) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction hr)⟩

theorem actualOriginalPathConstructorCases :
    OriginalVariableQuotientPathTargets.ActualOriginalPathConstructorCases := by
  intro p
  exact pathConstructorCases p.base p.window p.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathProof
