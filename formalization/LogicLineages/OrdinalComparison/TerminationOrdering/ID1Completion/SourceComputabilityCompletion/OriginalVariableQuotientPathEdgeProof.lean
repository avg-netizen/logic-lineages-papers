module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathEdgeCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathEdgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableQuotientPath OriginalVariableQuotientPathEdgeCoreProof
open OriginalVariableRepresentative (selectedData windowGraph)
open InternalParameterizedCanonicalResultFold (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- All three original certificate fields are bound by original Program
totality, then the actual quotient checker is factored internally. -/
theorem edgeRawCases (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α) (psi : Formula α)
    (he : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (s t k : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (requirements data oldStep (x.relabel j) (y.relabel j) s t k (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin 3 → Program 1 := Fin.cons source (Fin.cons target (Fin.cons step Fin.elim0))
  apply queryCases qs (Fin.cons certificate Fin.elim0) _
  intro β j ys Delta hj hq
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hf : Nonempty (Derivation body Delta (selectors (certificate.relabel j) (ys 0) (ys 1) (ys 2))) := by
    apply andIntro
    · have hvalue := hq 0
      rw [show qs (0 : Fin 3) = source from rfl] at hvalue
      simpa only [consTermRename,emptyRename] using hvalue
    · apply andIntro
      · have hvalue := hq 1
        rw [show qs (1 : Fin 3) = target from rfl] at hvalue
        simpa only [consTermRename,emptyRename] using hvalue
      · have hvalue := hq 2
        rw [show qs (2 : Fin 3) = step from rfl] at hvalue
        simpa only [consTermRename,emptyRename] using hvalue
  exact next β j Delta (ys 0) (ys 1) (ys 2) hj
    (checkerRecover data oldStep (x.relabel j) (y.relabel j) (certificate.relabel j)
      (ys 0) (ys 1) (ys 2) (parameter.relabel j) hf he')

theorem variableAtRaw (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y s t k typeCode parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hr : Nonempty (Derivation body Gamma
      (requirements (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y s t k parameter)))
    (hv : Nonempty (Derivation body Gamma (variableAccepted x)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x))) :
    Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode y typeCode)) := by
  apply programCases InternalUnpair.left (Fin.cons s Fin.elim0) _
  intro β j Delta typ hj hs
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hs
  have hw' := renameInto hw j Delta hj
  have hr' := renameInto hr j Delta hj
  have hv' := renameInto hv j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  rw [requirementsRename] at hr'
  simp only [variableAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv'
  rw [graph1Rename] at hl'
  exact variableAtRawType data window oldStep (x.relabel j) (y.relabel j)
    (s.relabel j) (t.relabel j) (k.relabel j) (typeCode.relabel j) typ (parameter.relabel j)
    hw' hr' hv' hl' hs

theorem bottomAtRaw (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y s t k parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hr : Nonempty (Derivation body Gamma
      (requirements (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y s t k parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomAccepted x))) :
    Nonempty (Derivation body Gamma ⊥) := by
  apply programCases InternalUnpair.left (Fin.cons s Fin.elim0) _
  intro β j Delta typ hj hs
  simp only [consTermRename,emptyRename] at hs
  have hw' := renameInto hw j Delta hj
  have hr' := renameInto hr j Delta hj
  have hb' := renameInto hb j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  rw [requirementsRename] at hr'
  simp only [bottomAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hb'
  exact bottomAtRawType data window oldStep (x.relabel j) (y.relabel j)
    (s.relabel j) (t.relabel j) (k.relabel j) typ (parameter.relabel j) hw' hr' hb' hs

theorem variableEdge (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y certificate parameter typeCode : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (he : Nonempty (Derivation body Gamma
      (edgeAccepted (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y certificate parameter)))
    (hv : Nonempty (Derivation body Gamma (variableAccepted x)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x))) :
    Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode y typeCode)) := by
  apply edgeRawCases (selectedData data window) (OriginalConstructorLeaf.refined oldStep)
    x y certificate parameter _ he
  intro β j Delta s t k hj hr
  rw [graph1Rename]
  have hw' := renameInto hw j Delta hj
  have hv' := renameInto hv j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [variableAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv'
  rw [graph1Rename] at hl'
  exact variableAtRaw data window oldStep (x.relabel j) (y.relabel j) s t k
    (typeCode.relabel j) (parameter.relabel j) hw' hr hv' hl'

theorem bottomEdgeContradiction (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y certificate parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomAccepted x)))
    (he : Nonempty (Derivation body Gamma
      (edgeAccepted (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y certificate parameter))) :
    Nonempty (Derivation body Gamma ⊥) := by
  apply edgeRawCases (selectedData data window) (OriginalConstructorLeaf.refined oldStep)
    x y certificate parameter _ he
  intro β j Delta s t k hj hr
  have hw' := renameInto hw j Delta hj
  have hb' := renameInto hb j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [bottomAccepted,graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hb'
  exact bottomAtRaw data window oldStep (x.relabel j) (y.relabel j) s t k
    (parameter.relabel j) hw' hr hb'

theorem quotientConstructorCases (data : Data) (window : Program 1) (oldStep : Program 4) :
    QuotientConstructorCases (selectedData data window) (OriginalConstructorLeaf.refined oldStep) window := by
  intro body α Delta x y certificate parameter typeCode
  constructor
  · let A := windowGraph window x parameter ⊓
      (edgeAccepted (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y certificate parameter ⊓
        (variableAccepted x ⊓ graph1 InternalUnpair.left typeCode x))
    have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hr⟩ := variableEdge data window oldStep x y certificate parameter typeCode
      (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
    exact ⟨Derivation.implicationIntroduction hr⟩
  · let A := windowGraph window x parameter ⊓ bottomAccepted x
    let E := edgeAccepted (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y certificate parameter
    have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hr⟩ := bottomEdgeContradiction data window oldStep x y certificate parameter
      (withHyp (andLeft h) E) (withHyp (andRight h) E)
      (show Nonempty (Derivation body (E :: A :: Delta) E) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction hr)⟩

theorem actualOriginalQuotientConstructorCases :
    OriginalVariableQuotientPathTargets.ActualOriginalQuotientConstructorCases := by
  intro p
  exact quotientConstructorCases p.base p.window p.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathEdgeProof
