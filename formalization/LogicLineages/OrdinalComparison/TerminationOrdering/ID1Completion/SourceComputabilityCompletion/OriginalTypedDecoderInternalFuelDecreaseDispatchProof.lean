module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSpecificationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof InternalAdditionLawsProof
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalDispatchSpecificationProof
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
open OriginalTypedDecoderInternalFuelDecreaseLeafProof
open OriginalTypedDecoderInternalFuelDecreaseBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem pairTagTransport (raw tag other payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (he : Nonempty (Derivation body Delta (equal tag other))) :
    Nonempty (Derivation body Delta (StepPair raw other payload)) := by
  apply headTransport InternalPairing.pairing raw tag other (Fin.cons payload Fin.elim0) ?_ hp
  simpa only [equalEqn] using he

 theorem termKnownDecrease (H : Program 1)
    (out gamma typ payload rest raw tail previous : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload)) →
      Nonempty (Derivation body Delta (termBranchSpec H out gamma typ payload rest i)) →
      Nonempty (Derivation body Delta (WorkFuelGraph tail rest)) →
      Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail))) →
      Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro hp h ht he
    exact variableDecrease out gamma typ payload rest raw tail previous h ht he
  ·
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hp h ht he
      exact lambdaDecrease out gamma typ payload rest raw tail previous hp h ht he
    ·
      refine Fin.cases ?_ (fun i => ?_) i
      · intro hp h ht he
        exact applicationDecrease out gamma typ payload rest raw tail previous hp h ht he
      ·
        refine Fin.cases ?_ (fun i => ?_) i
        · intro hp h ht he
          exact bottomDecrease out typ payload rest raw tail previous h ht he
        ·
          refine Fin.cases ?_ (fun i => ?_) i
          · intro hp h ht he
            exact ordinaryDecrease H out gamma typ payload rest raw tail previous hp h ht he
          ·
            refine Fin.cases ?_ (fun i => ?_) i
            · intro hp h ht he
              exact numberedDecrease H out gamma typ payload rest raw tail previous hp h ht he
            ·
              refine Fin.cases ?_ (fun i => ?_) i
              · intro hp h ht he
                exact failedIntro out previous h
              ·
                refine Fin.cases ?_ (fun i => ?_) i
                · intro hp h ht he
                  exact failedIntro out previous h
                ·
                  exact Fin.elim0 i

 theorem argumentsKnownDecrease
    (out gamma typ payload rest raw tail previous : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload)) →
      Nonempty (Derivation body Delta (argumentsBranchSpec out gamma typ payload rest i)) →
      Nonempty (Derivation body Delta (WorkFuelGraph tail rest)) →
      Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail))) →
      Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro hp h ht he
    exact failedIntro out previous h
  ·
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hp h ht he
      exact failedIntro out previous h
    ·
      refine Fin.cases ?_ (fun i => ?_) i
      · intro hp h ht he
        exact failedIntro out previous h
      ·
        refine Fin.cases ?_ (fun i => ?_) i
        · intro hp h ht he
          exact failedIntro out previous h
        ·
          refine Fin.cases ?_ (fun i => ?_) i
          · intro hp h ht he
            exact failedIntro out previous h
          ·
            refine Fin.cases ?_ (fun i => ?_) i
            · intro hp h ht he
              exact failedIntro out previous h
            ·
              refine Fin.cases ?_ (fun i => ?_) i
              · intro hp h ht he
                exact nilDecrease out typ payload rest raw tail previous h ht he
              ·
                refine Fin.cases ?_ (fun i => ?_) i
                · intro hp h ht he
                  exact consDecrease out gamma typ payload rest raw tail previous hp h ht he
                ·
                  exact Fin.elim0 i

 theorem termDecrease (H : Program 1)
    (out gamma typ tag payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (h : Nonempty (Derivation body Delta (StepTermDispatch H out gamma typ tag payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply termSpecCases H out gamma typ tag payload rest _ h
  · intro i Theta inc fields
    exact termKnownDecrease H out gamma typ payload rest raw tail previous i
      (pairTagTransport raw tag (numeral i.val) payload (weakenProof hp inc) (andLeft fields))
      (andRight fields) (weakenProof ht inc) (weakenProof he inc)
  · intro Theta inc fields
    exact failedIntro out previous (andRight fields)

 theorem argumentsDecrease 
    (out gamma typ tag payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (h : Nonempty (Derivation body Delta (StepArgumentsDispatch out gamma typ tag payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply argumentsSpecCases out gamma typ tag payload rest _ h
  · intro i Theta inc fields
    exact argumentsKnownDecrease out gamma typ payload rest raw tail previous i
      (pairTagTransport raw tag (numeral i.val) payload (weakenProof hp inc) (andLeft fields))
      (andRight fields) (weakenProof ht inc) (weakenProof he inc)
  · intro Theta inc fields
    exact failedIntro out previous (andRight fields)

/-- Mode and tag rejection stay explicit, so no typing or well-formedness
premise is needed for decrease of the actual original nonempty transition. -/
 theorem modeDecrease (H : Program 1)
    (out mode gamma typ tag payload rest raw tail previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (h : Nonempty (Derivation body Delta (StepModeDispatch H out mode gamma typ tag payload rest)))
    (ht : Nonempty (Derivation body Delta (WorkFuelGraph tail rest)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc raw) tail)))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply choiceCases h
  · intro Theta inc fields
    exact termDecrease H out gamma typ tag payload rest raw tail previous
      (weakenProof hp inc) (andRight fields) (weakenProof ht inc) (weakenProof he inc)
  · intro Theta inc alternatives
    apply choiceCases alternatives
    · intro Xi inc' fields
      exact argumentsDecrease out gamma typ tag payload rest raw tail previous
        (weakenProof (weakenProof hp inc) inc') (andRight fields)
        (weakenProof (weakenProof ht inc) inc') (weakenProof (weakenProof he inc) inc')
    · intro Xi inc' fields
      exact failedIntro out previous (andRight fields)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseDispatchProof
