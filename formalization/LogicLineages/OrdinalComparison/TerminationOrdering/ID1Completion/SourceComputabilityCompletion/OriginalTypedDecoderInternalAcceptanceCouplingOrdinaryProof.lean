module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingOrdinaryProof
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

/-- Couple the literal ordinary clause, keeping every original guard and field. -/
theorem ordinaryCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepOrdinary H out gamma typ payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .ordinary mode gamma typ tag payload rest joinedRest suffix)) := by
  apply stepOrdinaryCases H out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [localCoupledRename]
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  apply choiceCases (andRight (andRight (andRight fields)))
  · intro Xi inc accepted
    apply pushOneCases (numeral 1) (gamma.relabel j) (ys 4) (ys 1)
      (rest.relabel j) (joinedRest.relabel j) (suffix.relabel j) _ (weakenProof ha' inc)
    intro chi k Omega fw jw fs js hk happ hfs hjs hpush hjpush
    rw [localCoupledRename]
    have hf0 := renameInto (weakenProof (andLeft fields) inc) k Omega hk
    simp only [stepPairRename,consTermRename,emptyRename] at hf0
    have hf1 := renameInto (weakenProof (andLeft (andRight fields)) inc) k Omega hk
    simp only [programRename,consTermRename,emptyRename] at hf1
    have hvec : (fun i : Fin 1 => (![ys 0] i).relabel k) = ![(ys 0).relabel k] := by
      funext i
      exact Fin.cases rfl (fun i => Fin.elim0 i) i
    rw [hvec] at hf1
    have hf2 := renameInto (weakenProof (andLeft (andRight (andRight fields))) inc) k Omega hk
    simp only [stepArrowFieldsRename,consTermRename,emptyRename] at hf2
    have hg0 := renameInto (andLeft accepted) k Omega hk
    simp only [negativeRename,equalRename,numeral,sucRelabel,zRelabel] at hg0
    have hg1 := renameInto (andLeft (andRight accepted)) k Omega hk
    simp only [negativeRename,equalRename,numeral,sucRelabel,zRelabel] at hg1
    simp only [numeral,sucRelabel,zRelabel] at hpush hjpush
    exact localLiveIntro H .ordinary _ _ _ _ _ _ _ _ fw jw fs js happ hfs hjs
      (stepOrdinaryIntro H _ _ _ _ _ (fun i => (ys i).relabel k)
        (andIntro hf0 (andIntro hf1 (andIntro hf2 (orProofLeft (andIntro hg0 (andIntro hg1 hpush)))))))
      (stepOrdinaryIntro H _ _ _ _ _ (fun i => (ys i).relabel k)
        (andIntro hf0 (andIntro hf1 (andIntro hf2 (orProofLeft (andIntro hg0 (andIntro hg1 hjpush)))))))
  · intro Xi inc rejected
    exact localFailureIntro H .ordinary _ _ _ _ _ _ _ _
      (stepOrdinaryIntro H _ _ _ _ _ ys
        (andIntro (weakenProof (andLeft fields) inc) (andIntro (weakenProof (andLeft (andRight fields)) inc) (andIntro (weakenProof (andLeft (andRight (andRight fields))) inc) (orProofRight (andIntro (andLeft rejected) zeroEqual))))))
      (stepOrdinaryIntro H _ _ _ _ _ ys
        (andIntro (weakenProof (andLeft fields) inc) (andIntro (weakenProof (andLeft (andRight fields)) inc) (andIntro (weakenProof (andLeft (andRight (andRight fields))) inc) (orProofRight (andIntro (andLeft rejected) zeroEqual))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingOrdinaryProof
