module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingNumberedProof
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
open OriginalTypedDecoderInternalNumberedSyntaxProof

/-- The original successful numbered clause, with all nine witnesses explicit. -/
theorem numberedAcceptedIntro (H : Program 1)
    (out gamma typ payload rest : OTerm alpha) (ys : Fin 9 → OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (StepNumberedPayload payload (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5))))
    (hh : Nonempty (Derivation body Delta (programGraph H (ys 6) ![ys 1])))
    (ha : Nonempty (Derivation body Delta (StepArrowFields (ys 6) (ys 7) (ys 8))))
    (hn : Nonempty (Derivation body Delta (equal (ys 6) (numeral 0)).not))
    (he : Nonempty (Derivation body Delta (equal (ys 2) typ)))
    (hw : Nonempty (Derivation body Delta
      (StepPushTwo out (numeral 1) gamma (ys 8) (ys 3)
        (numeral 1) gamma (ys 4) (ys 5) rest))) :
    Nonempty (Derivation body Delta (StepNumbered H out gamma typ payload rest)) :=
  stepNumberedIntro H out gamma typ payload rest ys
    (andIntro hp (andIntro hh (andIntro ha (orProofLeft (andIntro hn (andIntro he hw))))))

theorem numberedRejectedIntro (H : Program 1)
    (gamma typ payload rest : OTerm alpha) (ys : Fin 9 → OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (StepNumberedPayload payload (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5))))
    (hh : Nonempty (Derivation body Delta (programGraph H (ys 6) ![ys 1])))
    (ha : Nonempty (Derivation body Delta (StepArrowFields (ys 6) (ys 7) (ys 8))))
    (hn : Nonempty (Derivation body Delta
      (equal (ys 6) (numeral 0) ⊔ (equal (ys 2) typ).not))) :
    Nonempty (Derivation body Delta (StepNumbered H z gamma typ payload rest)) :=
  stepNumberedIntro H z gamma typ payload rest ys
    (andIntro hp (andIntro hh (andIntro ha (orProofRight (andIntro hn zeroEqual)))))

/-- The two exact original requests are constructed ahead of the same suffix. -/
theorem numberedLiveCoupling (H : Program 1)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) (ys : Fin 9 → OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (StepNumberedPayload payload (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5))))
    (hh : Nonempty (Derivation body Delta (programGraph H (ys 6) ![ys 1])))
    (ha : Nonempty (Derivation body Delta (StepArrowFields (ys 6) (ys 7) (ys 8))))
    (hn : Nonempty (Derivation body Delta (equal (ys 6) (numeral 0)).not))
    (he : Nonempty (Derivation body Delta (equal (ys 2) typ)))
    (happend : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .numbered mode gamma typ tag payload rest joinedRest suffix)) := by
  apply pushTwoCases (numeral 1) gamma (ys 8) (ys 3) (numeral 1) gamma (ys 4) (ys 5)
    rest joinedRest suffix _ happend
  intro beta j Theta fw jw fs js hj happ hfs hjs hpush hjpush
  rw [localCoupledRename]
  have hp' := renameInto hp j Theta hj
  rw [stepNumberedPayloadRename] at hp'
  have hh' := renameInto hh j Theta hj
  rw [programRename] at hh'
  have hvec : (fun i : Fin 1 => (![ys 1] i).relabel j) = ![(ys 1).relabel j] := by
    funext i
    exact Fin.cases rfl (fun i => Fin.elim0 i) i
  rw [hvec] at hh'
  have ha' := renameInto ha j Theta hj
  rw [stepArrowFieldsRename] at ha'
  have hn' := renameInto hn j Theta hj
  simp only [negativeRename,equalRename,numeral,zRelabel] at hn'
  have he' := renameInto he j Theta hj
  rw [equalRename] at he'
  simp only [numeral,sucRelabel,zRelabel] at hpush hjpush
  have hs := numberedAcceptedIntro H fs (gamma.relabel j) (typ.relabel j)
    (payload.relabel j) (rest.relabel j) (fun i => (ys i).relabel j)
    hp' hh' ha' hn' he' hpush
  have hjspec := numberedAcceptedIntro H js (gamma.relabel j) (typ.relabel j)
    (payload.relabel j) (joinedRest.relabel j) (fun i => (ys i).relabel j)
    hp' hh' ha' hn' he' hjpush
  exact localLiveIntro H .numbered _ _ _ _ _ _ _ _ fw jw fs js happ hfs hjs hs hjspec

/-- Couple every numbered branch, preserving the recorded result test and
never adding equality to the decoded head result. -/
theorem numberedCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepNumbered H out gamma typ payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .numbered mode gamma typ tag payload rest joinedRest suffix)) := by
  apply stepNumberedCases H out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [localCoupledRename]
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  apply choiceCases (andRight (andRight (andRight fields)))
  · intro Xi inc accepted
    exact numberedLiveCoupling H (mode.relabel j) (gamma.relabel j) (typ.relabel j)
      (tag.relabel j) (payload.relabel j) (rest.relabel j) (joinedRest.relabel j) (suffix.relabel j) ys
      (weakenProof (andLeft fields) inc)
      (weakenProof (andLeft (andRight fields)) inc)
      (weakenProof (andLeft (andRight (andRight fields))) inc)
      (andLeft accepted) (andLeft (andRight accepted)) (weakenProof ha' inc)
  · intro Xi inc rejected
    have hp := weakenProof (andLeft fields) inc
    have hh := weakenProof (andLeft (andRight fields)) inc
    have harrow := weakenProof (andLeft (andRight (andRight fields))) inc
    exact localFailureIntro H .numbered _ _ _ _ _ _ _ _
      (numberedRejectedIntro H (gamma.relabel j) (typ.relabel j) (payload.relabel j)
        (rest.relabel j) ys hp hh harrow (andLeft rejected))
      (numberedRejectedIntro H (gamma.relabel j) (typ.relabel j) (payload.relabel j)
        (joinedRest.relabel j) ys hp hh harrow (andLeft rejected))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingNumberedProof
