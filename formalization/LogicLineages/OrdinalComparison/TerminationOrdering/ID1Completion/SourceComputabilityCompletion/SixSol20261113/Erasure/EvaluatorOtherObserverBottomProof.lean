module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNonApplicationSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomMeasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open GuardedSourceSyntaxProof (numeralRename)
open OriginalTypedDecoderTransportLogicalProof (iffForward)

theorem sourceBottomCode (H G : Program 1) (M W : Program 2)
    (input parameter : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 3) input)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (typ : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 BottomRepresentative.bottomCode (input.relabel j) typ)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply RankCalibrationBaseFieldsProof.leafCases 3 input psi ht
  intro beta j Theta typ raw field hj hp hc
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,numeralRename] at hs'
  let qs : Fin 2 → Program 1 := ![InternalUnpair.left,InternalUnpair.right]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (![parameter.relabel j]) _
  intro eta k Xi ys hk hq
  have hp' := renameInto hp k Xi hk
  have hc' := renameInto hc k Xi hk
  have hs'' := renameInto hs' k Xi hk
  simp only [graph1Rename,graph2Rename,numeralRename] at hp' hc' hs''
  have hq0 : Nonempty (Derivation body Xi
      (graph1 InternalUnpair.left (ys 0) ((parameter.relabel j).relabel k))) := by
    simpa only [qs,consTermRename,emptyRename] using hq 0
  have hq1 : Nonempty (Derivation body Xi
      (graph1 InternalUnpair.right (ys 1) ((parameter.relabel j).relabel k))) := by
    simpa only [qs,consTermRename,emptyRename] using hq 1
  have hparam := reconstructPair ((parameter.relabel j).relabel k) (ys 0) (ys 1) hq0 hq1
  have ha := OriginalTransparentDecoderValidatorCollapsePackedProof.sourceFieldsElim H G M W
    ((input.relabel j).relabel k) ((parameter.relabel j).relabel k) (typ.relabel k) (raw.relabel k)
    (ys 0) (ys 1) hp' hparam hs''
  have hraw := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 3) (.projection 0)
    (raw.relabel k) (numeral 3) (field.relabel k) (![field.relabel k]) hc'
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 3 (![field.relabel k]))
    (projectionValue 0 (![field.relabel k]))
  have he := andRight (iffForward (OriginalUniverseDecoderInternalAcceptanceLeafProof.bottomIff H M W
    (raw.relabel k) (field.relabel k) (typ.relabel k) (ys 1) (ys 0) hraw) (andRight ha))
  simp only [equalEqn] at he
  have hcTyp := headTransport (pairOf (OriginalRawSyntaxTransport.constant 1 3) (.projection 0))
    (raw.relabel k) (field.relabel k) (typ.relabel k) Fin.elim0 he hc'
  have hb : Nonempty (Derivation body Xi
      (graph1 BottomRepresentative.bottomCode ((input.relabel j).relabel k) (typ.relabel k))) :=
    binaryValue InternalPairing.pairing (.projection 0)
      (pairOf (BottomRepresentative.constant 3) (.projection 0))
      ((input.relabel j).relabel k) (typ.relabel k) (raw.relabel k) (![typ.relabel k]) hp'
      (projectionValue 0 (![typ.relabel k])) hcTyp
  have ans := next eta (k ∘ j) Xi (typ.relabel k)
    (fun f hf => by simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk _ (hj f hf))
    (by simpa only [Term.relabel_relabel] using hb)
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using ans
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverBottomProof
