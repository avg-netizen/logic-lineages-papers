module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalNeutralLeaf InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (OTerm z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Transfer the unchanged original Context test from the binary parameter
reader to the actual four leaf coordinates. Its Context value is bound
internally by arithmetic Program totality. -/
theorem windowValue (window : Program 1) (source target certificate parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) (suc z) source parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (windowAt window) (suc z) source target certificate parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons parameter Fin.elim0) _
  intro beta j Theta context hj hc
  rw [graph4Rename]
  simp only [sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hc
  have hw' := renameInto hw j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hw'
  let ys : Fin 2 → OTerm beta :=
    Fin.cons (source.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  let xs : Fin 4 → OTerm beta := Fin.cons (source.relabel j)
    (Fin.cons (target.relabel j) (Fin.cons (certificate.relabel j)
      (Fin.cons (parameter.relabel j) Fin.elim0)))
  have hctx := unaryValue InternalUnpair.left (.projection 1) context
    (parameter.relabel j) ys hc (projectionValue 1 ys)
  have hraw := unaryRecover window (leftOf (.projection 1)) (suc z) context ys hw' hctx
  exact unaryValue window (leftOf (.projection 3)) (suc z) context xs hraw
    (unaryValue InternalUnpair.left (.projection 3) context (parameter.relabel j) xs hc
      (projectionValue 3 xs))

theorem triggerValue (endpoint : Program 6) (window : Program 1)
    (source target certificate parameter state : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 edgeCode state source target certificate)))
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) (suc z) source parameter)))
    (hn : Nonempty (Derivation body Delta (graph1 neutralTest (suc z) source)))
    (hz : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationStepChecker.guardP endpoint) z state parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (trigger endpoint window) (suc z) source target certificate parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons source
    (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hg : Nonempty (Derivation body Delta (programGraph (guardAt endpoint) z xs)) :=
    binaryValue (InternalParameterizedApplicationStepChecker.guardP endpoint)
      InternalParameterizedApplicationStepChecker.edgeStateP (.projection 3)
      z state parameter xs hz
      (InternalParameterizedApplicationStepCheckerGraphProof.edgeStateValue
        state source target certificate parameter he) (projectionValue 3 xs)
  exact conjunctionAccept (windowAt window)
    (InternalAcceptance.conjunction neutralAt
      (InternalApplicationStepPeel.same (guardAt endpoint) (InternalAcceptance.constantZero 4))) xs
    (windowValue window source target certificate parameter hw)
    (conjunctionAccept neutralAt
      (InternalApplicationStepPeel.same (guardAt endpoint) (InternalAcceptance.constantZero 4)) xs
      (unaryValue neutralTest (.projection 0) (suc z) source xs hn (projectionValue 0 xs))
      (sameAccept (guardAt endpoint) (InternalAcceptance.constantZero 4) z xs hg
        (constantZeroValue xs)))

theorem originalFactor (endpoint : Program 6) (window : Program 1) (oldStep : Program 4) :
    OriginalConstructorLeaf.OriginalFactor oldStep (refined endpoint window oldStep) := by
  intro body alpha Delta source target certificate parameter
  let P := OriginalConstructorLeaf.accepted (refined endpoint window oldStep)
    source target certificate parameter
  let xs : Fin 4 → OTerm alpha := Fin.cons source
    (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := andLeft (conjunctionRecover oldStep (leafGuard endpoint window) xs hp)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Actual branch elimination yields the same-type original bottom, with
the old leaf and original raw arguments retained throughout. -/
theorem neutralBottom (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
    (source target certificate parameter state typeCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (OriginalConstructorLeaf.accepted (refined endpoint window oldStep)
        source target certificate parameter)))
    (he : Nonempty (Derivation body Delta (graph3 edgeCode state source target certificate)))
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) (suc z) source parameter)))
    (hn : Nonempty (Derivation body Delta (graph1 neutralTest (suc z) source)))
    (hz : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationStepChecker.guardP endpoint) z state parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typeCode source))) :
    Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode target typeCode)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons source
    (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hl := andRight (conjunctionRecover oldStep (leafGuard endpoint window) xs ha)
  have hs := successorBranchElim (trigger endpoint window) (InternalLessThan.constantOne 4)
    (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom)
    (suc z) z xs (triggerValue endpoint window source target certificate parameter state he hw hn hz) hl
  have hb := OriginalConstructorLeafInternalProof.sameKnownLeftRecover
    (.projection 1) OriginalConstructorLeaf.expectedBottom target xs hs (projectionValue 1 xs)
  exact unaryRecover BottomRepresentative.bottomCode (leftOf (.projection 0)) target typeCode xs hb
    (unaryValue InternalUnpair.left (.projection 0) typeCode source xs ht (projectionValue 0 xs))

theorem neutralLaw (endpoint : Program 6) (window : Program 1) (oldStep : Program 4) :
    NeutralBottom endpoint window (refined endpoint window oldStep) := by
  intro body alpha Delta source target certificate parameter state typeCode
  let P := OriginalConstructorLeaf.accepted (refined endpoint window oldStep)
    source target certificate parameter ⊓
    (graph3 edgeCode state source target certificate ⊓
      (graph2 (BottomRepresentative.windowAt window) (suc z) source parameter ⊓
        (graph1 neutralTest (suc z) source ⊓
          (graph2 (InternalParameterizedApplicationStepChecker.guardP endpoint) z state parameter ⊓
            graph1 InternalUnpair.left typeCode source))))
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 := andRight hp
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  obtain ⟨h⟩ := neutralBottom endpoint window oldStep source target certificate parameter state typeCode
    (andLeft hp) (andLeft h1) (andLeft h2) (andLeft h3) (andLeft h4) (andRight h4)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalNeutralLeafInternalCases :
    OriginalNeutralLeafTargets.ActualOriginalNeutralLeafInternalCases := by
  intro endpoint window oldStep
  exact ⟨originalFactor endpoint window oldStep,neutralLaw endpoint window oldStep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafInternalProof
