module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof (stepPairRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalTransparentLambdaValidityInternal (TagIs)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem atPairs (H G : Program 1) (M W : Program 2)
    (packed parameter typ raw c gamma payload : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hr : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload)))
    (hs : Nonempty (Derivation body Gamma
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter))) :
    Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) packed)) := by
  obtain ⟨heq⟩ := sourceEquation H G M W packed parameter typ raw c gamma hp hc
  obtain ⟨hs⟩ := hs
  have accepted := Derivation.conjunctionRight
    (Derivation.implicationElimination (Derivation.conjunctionLeft heq) hs)
  obtain ⟨hb⟩ := OriginalUniverseDecoderInternalAcceptanceLeafProof.bottomIff H M W raw payload typ gamma c hr
  have eqPayload := Derivation.conjunctionRight
    (Derivation.implicationElimination (Derivation.conjunctionLeft hb) accepted)
  have rightTyp := outputTransport InternalUnpair.right payload typ (Fin.cons raw Fin.elim0)
    ⟨by simpa only [equalEqn] using eqPayload⟩ (pairRight raw (numeral 3) payload hr)
  have rawPair := reconstructPair raw (numeral 3) typ (pairLeft raw (numeral 3) payload hr) rightTyp
  let xs : Fin 1 → OTerm alpha := Fin.cons typ Fin.elim0
  have pay : Nonempty (Derivation body Gamma (graph1 BottomSourceShapeProof.bottomPayload raw typ)) :=
    binaryValue InternalPairing.pairing (BottomRepresentative.constant 3) (.projection 0)
      raw (numeral 3) typ xs rawPair (BottomSourceValidityProof.constantValue 3 xs) (projectionValue 0 xs)
  have code : Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode packed typ)) := by
    rw [BottomSourceShapeProof.bottomCodeProgram]
    exact binaryValue InternalPairing.pairing (.projection 0) BottomSourceShapeProof.bottomPayload
      packed typ raw xs hp (projectionValue 0 xs) pay
  exact BottomSourceShapeProof.bottomAccept packed typ code

theorem sourceTagBottom (H G : Program 1) (M W : Program 2) (packed parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
    (ht : Nonempty (Derivation body Gamma (TagIs 3 packed))) :
    Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) packed)) := by
  let qs : Fin 5 → Program 2 := ![leftOf (.projection 0),rightOf (.projection 0),
    leftOf (.projection 1),rightOf (.projection 1),rightOf (rightOf (.projection 0))]
  let xs : Fin 2 → OTerm alpha := ![packed,parameter]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,numeralRename] at hs'
  have ht' := renameInto ht j Theta hj
  simp only [TagIs,graph1Rename,numeralRename] at ht'
  simp only [BottomRepresentative.bottomGraph,graph1Rename,numeralRename]
  let xx : Fin 2 → OTerm beta := fun i => (xs i).relabel j
  have hleft := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (packed.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have hright := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (packed.relabel j) xx
    (hq 1) (projectionValue 0 xx)
  have hcontext := unaryRecover InternalUnpair.left (.projection 1) (ys 2) (parameter.relabel j) xx
    (hq 2) (projectionValue 1 xx)
  have hgamma := unaryRecover InternalUnpair.right (.projection 1) (ys 3) (parameter.relabel j) xx
    (hq 3) (projectionValue 1 xx)
  have hpayload := unaryRecover InternalUnpair.right (rightOf (.projection 0)) (ys 4) (ys 1) xx
    (hq 4) (hq 1)
  have hp := reconstructPair (packed.relabel j) (ys 0) (ys 1) hleft hright
  have hc := reconstructPair (parameter.relabel j) (ys 2) (ys 3) hcontext hgamma
  have hr := rawTagPair (packed.relabel j) (ys 0) (ys 1) (numeral 3) (ys 4) hp ht' hpayload
  exact atPairs H G M W (packed.relabel j) (parameter.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hp hc hr hs'

theorem concreteSourceNotTagThree (H G : Program 1) (M W : Program 2) (packed parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
    (hn : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) packed).not)) :
    Nonempty (Derivation body Gamma (TagIs 3 packed).not) := by
  let A := TagIs 3 packed
  obtain ⟨hb⟩ := sourceTagBottom H G M W packed parameter (addAssumption hs A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hn⟩ := addAssumption hn A
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hb)⟩

theorem actualSourceTagBottom : OriginalTransparentDirectBottomSourceTargets.ActualSourceTagBottom := by
  intro H G M W body alpha Gamma packed parameter
  let A := graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter ⊓ TagIs 3 packed
  have h : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := sourceTagBottom H G M W packed parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hb⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceProof.actualSourceTagBottom
