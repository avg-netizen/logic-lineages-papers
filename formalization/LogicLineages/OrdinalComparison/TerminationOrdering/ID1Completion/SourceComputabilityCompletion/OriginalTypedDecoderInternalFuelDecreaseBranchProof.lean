module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreasePayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalConsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open InternalPairingSumBounds
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalFuelSupportProof
open OriginalTypedDecoderInternalLambdaSyntaxProof OriginalTypedDecoderInternalOrdinarySyntaxProof
open OriginalTypedDecoderInternalNumberedSyntaxProof OriginalTypedDecoderInternalApplicationSyntaxProof
open OriginalTypedDecoderInternalConsSyntaxProof
open OriginalTypedDecoderInternalFuelChildBoundsProof
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
open OriginalTypedDecoderInternalFuelDecreasePushProof
open OriginalTypedDecoderInternalFuelDecreaseLeafProof
open OriginalTypedDecoderInternalFuelDecreasePayloadProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem lambdaDecrease 
    (out gamma typ payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 1) payload)))
    (h : Nonempty (Derivation body Delta (StepLambda out gamma typ payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepLambdaCases out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hb := lambdaBound (raw.relabel j) (payload.relabel j) (ys 0) (ys 1)
    hp' (andLeft fields)
  apply choiceCases (andRight (andRight (andRight fields)))
  · intro Xi inc accepted
    exact pushedOneDecrease (out.relabel j) (numeral 0) (ys 4) (ys 3) (ys 1)
      (rest.relabel j) (raw.relabel j) (tail.relabel j) (previous.relabel j)
      (andRight (andRight accepted)) (weakenProof ht' inc)
      (weakenProof hb inc) (weakenProof he' inc)
  · intro Xi inc rejected
    exact failedIntro (out.relabel j) (previous.relabel j) (andRight rejected)

 theorem ordinaryDecrease (H : Program 1)
    (out gamma typ payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 4) payload)))
    (h : Nonempty (Derivation body Delta (StepOrdinary H out gamma typ payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepOrdinaryCases H out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hb := ordinaryBound (raw.relabel j) (payload.relabel j) (ys 0) (ys 1)
    hp' (andLeft fields)
  apply choiceCases (andRight (andRight (andRight fields)))
  · intro Xi inc accepted
    exact pushedOneDecrease (out.relabel j) (numeral 1) (gamma.relabel j) (ys 4) (ys 1)
      (rest.relabel j) (raw.relabel j) (tail.relabel j) (previous.relabel j)
      (andRight (andRight accepted)) (weakenProof ht' inc)
      (weakenProof hb inc) (weakenProof he' inc)
  · intro Xi inc rejected
    exact failedIntro (out.relabel j) (previous.relabel j) (andRight rejected)

 theorem applicationDecrease (out gamma typ payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 2) payload)))
    (h : Nonempty (Derivation body Delta (StepApplication out gamma typ payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepApplicationCases out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hb := applicationPayloadBound (raw.relabel j) (payload.relabel j) (ys 0) (ys 1) (ys 2)
    hp' (andLeft fields)
  exact pushedTwoDecrease (out.relabel j) (numeral 0) (gamma.relabel j) (ys 3) (ys 1)
    (numeral 0) (gamma.relabel j) (ys 0) (ys 2) (rest.relabel j) (raw.relabel j)
    (tail.relabel j) (previous.relabel j) (andRight (andRight fields)) ht' hb he'

 theorem consDecrease (out gamma typ payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 7) payload)))
    (h : Nonempty (Derivation body Delta (StepArgumentsCons out gamma typ payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepArgumentsConsCases out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hb := consPayloadBound (raw.relabel j) (payload.relabel j) (ys 0) (ys 1) (ys 2)
    hp' (andLeft fields)
  apply choiceCases (andRight (andRight fields))
  · intro Xi inc accepted
    exact pushedTwoDecrease (out.relabel j) (numeral 0) (gamma.relabel j) (ys 0) (ys 1)
      (numeral 1) (gamma.relabel j) (ys 4) (ys 2) (rest.relabel j) (raw.relabel j)
      (tail.relabel j) (previous.relabel j) (andRight (andRight accepted))
      (weakenProof ht' inc) (weakenProof hb inc) (weakenProof he' inc)
  · intro Xi inc rejected
    exact failedIntro (out.relabel j) (previous.relabel j) (andRight rejected)

 theorem numberedDecrease (H : Program 1)
    (out gamma typ payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
    (h : Nonempty (Derivation body Delta (StepNumbered H out gamma typ payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply stepNumberedCases H out gamma typ payload rest _ h
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have hp' := renameInto hp j Theta hj
  simp only [stepPairRename,numeral,sucRelabel,zRelabel] at hp'
  have ht' := renameInto ht j Theta hj
  rw [fuelRename] at ht'
  have he' := renameInto he j Theta hj
  simp only [eqnRelabel,addRelabel,sucRelabel] at he'
  have hb := numberedPayloadBound (raw.relabel j) (payload.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hp' (andLeft fields)
  apply choiceCases (andRight (andRight (andRight fields)))
  · intro Xi inc accepted
    exact pushedTwoDecrease (out.relabel j) (numeral 1) (gamma.relabel j) (ys 8) (ys 3)
      (numeral 1) (gamma.relabel j) (ys 4) (ys 5) (rest.relabel j) (raw.relabel j)
      (tail.relabel j) (previous.relabel j) (andRight (andRight accepted))
      (weakenProof ht' inc) (weakenProof hb inc) (weakenProof he' inc)
  · intro Xi inc rejected
    exact failedIntro (out.relabel j) (previous.relabel j) (andRight rejected)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseBranchProof
