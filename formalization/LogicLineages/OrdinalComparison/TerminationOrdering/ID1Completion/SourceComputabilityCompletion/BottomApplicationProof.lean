module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalBetaTotalityProof (addHyp)
open InternalParameterizedCanonicalResultFoldOpeningProof InternalParameterizedCanonicalResultFoldConsumerProof
open InternalOriginalUniformApplicationTypingApplicationProof
open SourceComputabilityCompletion.BottomRepresentative
open SourceComputabilityCompletion.BottomDescentSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem notBottomRename {β : Type} (value : OrdinaryArithmetic.Term α) (j : α → β) :
    ((bottomGraph (suc z) value).not).relabel j = (bottomGraph (suc z) (value.relabel j)).not := by
  change ((bottomGraph (suc z) value).relabel j).not = _
  rw [bottomRename,sucRelabel,zRelabel]

theorem packedNotBottom (d e fp ap value : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap))) :
    Nonempty (Derivation body Gamma (bottomGraph (suc z) value).not) := by
  let P := bottomGraph (suc z) value
  let tag : Program 1 := InternalApplicationStepPeel.constructorTag (.projection 0)
  have hl := InternalCanonicalResultFoldInvariantApplicationSupportProof.packedLeft d e fp ap value hp
  have ht := InternalParameterizedApplicationResultStackVisitSupportProof.rootTagAccept d e fp ap value hp
  obtain ⟨hl⟩ := hl
  obtain ⟨ht⟩ := ht
  have hc := BottomSourceShapeProof.bottomRecover (body := body) (Gamma := P :: Gamma) value e
    ⟨addHyp hl P⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hthree := BottomSourceValidityProof.bottomConstructorTag value e hc
  have htwo := sameRightRecover tag (two 1) positionTerm (Fin.cons value Fin.elim0)
    ⟨addHyp ht P⟩ (twoValue (Fin.cons value Fin.elim0))
  obtain ⟨he⟩ := valueUnique tag positionTerm (numeral 3) (Fin.cons value Fin.elim0) htwo hthree
  rw [positionTermEq] at he
  change Derivation body (P :: Gamma) (eqn (suc (suc z)) (suc (suc (suc z)))) at he
  exact ⟨Derivation.implicationIntroduction (zeroNeSuc (cancelSuc (cancelSuc he)))⟩

theorem rawNotBottom (d e f a value : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (graph4 application value d e f a))) :
    Nonempty (Derivation body Gamma (bottomGraph (suc z) value).not) := by
  let qs : Fin 2 → Program 2 := Fin.cons (rightOf (.projection 0))
    (Fin.cons (rightOf (.projection 1)) Fin.elim0)
  let xs : Fin 2 → OrdinaryArithmetic.Term α := Fin.cons f (Fin.cons a Fin.elim0)
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  rw [notBottomRename]
  have hp' := renameInto hp j Delta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OrdinaryArithmetic.Term β := Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)
  have hfr := unaryRecover InternalUnpair.right (.projection (0 : Fin 2)) (ys 0)
    (f.relabel j) xx (hq 0) (projectionValue 0 xx)
  have har := unaryRecover InternalUnpair.right (.projection (1 : Fin 2)) (ys 1)
    (a.relabel j) xx (hq 1) (projectionValue 1 xx)
  have hpacked := applicationForward (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j)
    (ys 0) (ys 1) (value.relabel j) hfr har hp'
  exact packedNotBottom (d.relabel j) (e.relabel j) (ys 0) (ys 1) (value.relabel j) hpacked

/-- Only existing canonical-fold output invariants are used for the raw
argument. The function is the caller's original supplied function. -/
theorem atRaw (data : Data) (window : Program 1)
    (arrow d e f a out parameter b raw : OrdinaryArithmetic.Term α)
    (hwindow : Nonempty (Derivation body Gamma (graph2 (windowAt window) (suc z) f parameter)))
    (h : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (readyData data window)
        arrow d e f a out parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (readyData data window) b a parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e f b))) :
    Nonempty (Derivation body Gamma (bottomGraph (suc z) out).not) := by
  let selected := readyData data window
  have har := andLeft h
  have hm := andLeft (andRight h)
  have hf := andLeft (andRight (andRight h))
  have ha := andLeft (andRight (andRight (andRight h)))
  have hj := andRight (andRight (andRight (andRight h)))
  have hff := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    selected.oldRepresentative (InternalOriginalUniformDescentSelection.validity selected) selected.member
    f arrow parameter hf
  have haf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    selected.oldRepresentative (InternalOriginalUniformDescentSelection.validity selected) selected.member
    a d parameter ha
  have hb := andRight (certifiedAt selected b a d parameter
    (andLeft (andRight haf)) (andLeft (andRight (andRight haf))) hn)
  have hv := rawValidity selected arrow d e f b raw parameter har
    (andLeft (andRight (andRight hff))) (andLeft (andRight hb)) hm
    (andLeft (andRight hff)) (andLeft hb) hr
  have hd := combineRecover selected d e f b raw out parameter hr
    (applicationCombine selected d e f a out parameter b hn hj)
  have hwraw := BottomDescentStepProof.windowChange window (suc z) f raw parameter hwindow
  have hactive : Nonempty (Derivation body Gamma (activeGraph data window raw parameter)) :=
    conjunctionAccept (windowAt window) (BottomDescent.selectedValidity data window)
      (Fin.cons raw (Fin.cons parameter Fin.elim0)) hwraw hv
  obtain ⟨hshape⟩ := BottomDescentProof.selectedIff data window out raw parameter (suc z) hactive hd
  obtain ⟨hnot⟩ := rawNotBottom d e f b raw hr
  let P := bottomGraph (suc z) out
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (addHyp hnot P)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hshape) P)
        (Derivation.hypothesis List.mem_cons_self)))⟩

theorem atArgument (data : Data) (window : Program 1)
    (arrow d e f a out parameter b : OrdinaryArithmetic.Term α)
    (hw : Nonempty (Derivation body Gamma (graph2 (windowAt window) (suc z) f parameter)))
    (h : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (readyData data window)
        arrow d e f a out parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (readyData data window) b a parameter))) :
    Nonempty (Derivation body Gamma (bottomGraph (suc z) out).not) := by
  apply programCases application (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons b Fin.elim0)))) _
  intro β j Delta raw hj hr
  rw [notBottomRename]
  have hw' := renameInto hw j Delta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hw'
  have h' := renameInto h j Delta hj
  rw [applicationPremisesRename] at h'
  have hn' := renameInto hn j Delta hj
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename] at hn'
  simp only [consTermRename,emptyRename] at hr
  exact atRaw data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (out.relabel j) (parameter.relabel j) (b.relabel j) raw hw' h' hn' hr

theorem applicationNonBottom (data : Data) (window : Program 1)
    (arrow d e f a out parameter : OrdinaryArithmetic.Term α)
    (hw : Nonempty (Derivation body Gamma (graph2 (windowAt window) (suc z) f parameter)))
    (h : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (readyData data window)
        arrow d e f a out parameter))) :
    Nonempty (Derivation body Gamma (bottomGraph (suc z) out).not) := by
  apply programCases (InternalParameterizedCanonicalResultFold.foldN (readyData data window))
    (Fin.cons a (Fin.cons parameter Fin.elim0)) _
  intro β j Delta b hj hn
  rw [notBottomRename]
  have hw' := renameInto hw j Delta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hw'
  have h' := renameInto h j Delta hj
  rw [applicationPremisesRename] at h'
  simp only [consTermRename,emptyRename] at hn
  exact atArgument data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (out.relabel j) (parameter.relabel j) b hw' h' hn

theorem actualParameterizedApplicationNonBottom : BottomApplicationTargets.ActualParameterizedApplicationNonBottom := by
  intro body data window α Delta arrow d e f a out parameter
  let P := graph2 (windowAt window) (suc z) f parameter ⊓
    InternalOriginalUniformApplicationTyping.applicationPremises (readyData data window)
      arrow d e f a out parameter
  have h : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := applicationNonBottom data window arrow d e f a out parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomApplicationProof
