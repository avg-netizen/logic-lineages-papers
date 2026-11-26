module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
open OriginalTypedDecoderInternalAcceptanceCouplingPushProof
open OriginalTypedDecoderInternalLogicSyntaxProof OriginalTypedDecoderInternalVariableSyntaxProof
open OriginalTypedDecoderInternalFuelDecreaseLeafProof
open OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
open OriginalTypedDecoderInternalLambdaSyntaxProof OriginalTypedDecoderInternalOrdinarySyntaxProof
open OriginalTypedDecoderInternalNumberedSyntaxProof OriginalTypedDecoderInternalApplicationSyntaxProof
open OriginalTypedDecoderInternalConsSyntaxProof OriginalTypedDecoderInternalBinarySyntaxProof

/-- Couple the literal application clause, keeping every original guard and field. -/
theorem applicationCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepApplication out gamma typ payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .application mode gamma typ tag payload rest joinedRest suffix)) := by
  apply stepApplicationCases out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [localCoupledRename]
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  apply pushTwoCases (numeral 0) (gamma.relabel j) (ys 3) (ys 1) (numeral 0) (gamma.relabel j) (ys 0) (ys 2)
    (rest.relabel j) (joinedRest.relabel j) (suffix.relabel j) _ ha'
  intro chi k Omega fw jw fs js hk happ hfs hjs hpush hjpush
  rw [localCoupledRename]
  have hf0 := renameInto (andLeft fields) k Omega hk
  simp only [stepBinaryPayloadRename,consTermRename,emptyRename] at hf0
  have hf1 := renameInto (andLeft (andRight fields)) k Omega hk
  simp only [stepConsRename,consTermRename,emptyRename] at hf1
  simp only [numeral,sucRelabel,zRelabel] at hpush hjpush
  exact localLiveIntro H .application _ _ _ _ _ _ _ _ fw jw fs js happ hfs hjs
    (stepApplicationIntro _ _ _ _ _ (fun i => (ys i).relabel k)
      (andIntro hf0 (andIntro hf1 hpush)))
    (stepApplicationIntro _ _ _ _ _ (fun i => (ys i).relabel k)
      (andIntro hf0 (andIntro hf1 hjpush)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingApplicationProof
