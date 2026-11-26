module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingDispatchProof
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
open OriginalTypedDecoderInternalAcceptanceCouplingMapProof
open OriginalTypedDecoderInternalAcceptanceCouplingLambdaProof
open OriginalTypedDecoderInternalAcceptanceCouplingOrdinaryProof
open OriginalTypedDecoderInternalAcceptanceCouplingNumberedProof
open OriginalTypedDecoderInternalAcceptanceCouplingApplicationProof
open OriginalTypedDecoderInternalAcceptanceCouplingConsProof
open OriginalTypedDecoderInternalDispatchSpecificationProof


theorem numeralRelabelAll {beta : Type} (n : Nat) (j : alpha → beta) :
    (numeral n : OTerm alpha).relabel j = numeral n := by
  induction n with
  | zero => exact zRelabel j
  | succ n ih => simpa only [numeral,sucRelabel] using congrArg suc ih

theorem termKnownCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (equal tag (numeral i.val))) →
      Nonempty (Derivation body Delta (termBranchSpec H out gamma typ payload rest i)) →
      Nonempty (Derivation body Delta
        (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix)) →
      Nonempty (Derivation body Delta (CoupledLocal H .terms mode gamma typ tag payload rest joinedRest suffix)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ht hs ha
    apply mapCoupling H .variable .terms mode gamma typ tag payload rest joinedRest suffix
      (variableCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
    intro beta j Theta next tail hj hn
    have ht' := renameInto ht j Theta hj
    simp only [equalRename,numeralRelabelAll] at ht'
    exact termSpecIntro H next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
      (payload.relabel j) tail (0 : Fin 8) (andIntro ht' hn)
  ·
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ht hs ha
      apply mapCoupling H .lambda .terms mode gamma typ tag payload rest joinedRest suffix
        (lambdaCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
      intro beta j Theta next tail hj hn
      have ht' := renameInto ht j Theta hj
      simp only [equalRename,numeralRelabelAll] at ht'
      exact termSpecIntro H next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
        (payload.relabel j) tail (1 : Fin 8) (andIntro ht' hn)
    ·
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ht hs ha
        apply mapCoupling H .application .terms mode gamma typ tag payload rest joinedRest suffix
          (applicationCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
        intro beta j Theta next tail hj hn
        have ht' := renameInto ht j Theta hj
        simp only [equalRename,numeralRelabelAll] at ht'
        exact termSpecIntro H next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
          (payload.relabel j) tail (2 : Fin 8) (andIntro ht' hn)
      ·
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ht hs ha
          apply mapCoupling H .bottom .terms mode gamma typ tag payload rest joinedRest suffix
            (bottomCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
          intro beta j Theta next tail hj hn
          have ht' := renameInto ht j Theta hj
          simp only [equalRename,numeralRelabelAll] at ht'
          exact termSpecIntro H next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
            (payload.relabel j) tail (3 : Fin 8) (andIntro ht' hn)
        ·
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ht hs ha
            apply mapCoupling H .ordinary .terms mode gamma typ tag payload rest joinedRest suffix
              (ordinaryCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
            intro beta j Theta next tail hj hn
            have ht' := renameInto ht j Theta hj
            simp only [equalRename,numeralRelabelAll] at ht'
            exact termSpecIntro H next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
              (payload.relabel j) tail (4 : Fin 8) (andIntro ht' hn)
          ·
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ht hs ha
              apply mapCoupling H .numbered .terms mode gamma typ tag payload rest joinedRest suffix
                (numberedCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
              intro beta j Theta next tail hj hn
              have ht' := renameInto ht j Theta hj
              simp only [equalRename,numeralRelabelAll] at ht'
              exact termSpecIntro H next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
                (payload.relabel j) tail (5 : Fin 8) (andIntro ht' hn)
            ·
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ht hs ha
                exact localFailureIntro H .terms _ _ _ _ _ _ _ _
                  (termSpecIntro H z gamma typ tag payload rest (6 : Fin 8) (andIntro ht zeroEqual))
                  (termSpecIntro H z gamma typ tag payload joinedRest (6 : Fin 8) (andIntro ht zeroEqual))
              ·
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ht hs ha
                  exact localFailureIntro H .terms _ _ _ _ _ _ _ _
                    (termSpecIntro H z gamma typ tag payload rest (7 : Fin 8) (andIntro ht zeroEqual))
                    (termSpecIntro H z gamma typ tag payload joinedRest (7 : Fin 8) (andIntro ht zeroEqual))
                ·
                  exact Fin.elim0 i

theorem termCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepTermDispatch H out gamma typ tag payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .terms mode gamma typ tag payload rest joinedRest suffix)) := by
  apply termSpecCases H out gamma typ tag payload rest _ h
  · intro i Theta inc fields
    exact termKnownCoupling H out mode gamma typ tag payload rest joinedRest suffix i
      (andLeft fields) (andRight fields) (weakenProof ha inc)
  · intro Theta inc fields
    exact localFailureIntro H .terms _ _ _ _ _ _ _ _
      (termSpecFallback H z gamma typ tag payload rest (andIntro (andLeft fields) zeroEqual))
      (termSpecFallback H z gamma typ tag payload joinedRest (andIntro (andLeft fields) zeroEqual))

theorem argumentsKnownCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (equal tag (numeral i.val))) →
      Nonempty (Derivation body Delta (argumentsBranchSpec out gamma typ payload rest i)) →
      Nonempty (Derivation body Delta
        (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix)) →
      Nonempty (Derivation body Delta (CoupledLocal H .arguments mode gamma typ tag payload rest joinedRest suffix)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ht hs ha
    exact localFailureIntro H .arguments _ _ _ _ _ _ _ _
      (argumentsSpecIntro z gamma typ tag payload rest (0 : Fin 8) (andIntro ht zeroEqual))
      (argumentsSpecIntro z gamma typ tag payload joinedRest (0 : Fin 8) (andIntro ht zeroEqual))
  ·
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ht hs ha
      exact localFailureIntro H .arguments _ _ _ _ _ _ _ _
        (argumentsSpecIntro z gamma typ tag payload rest (1 : Fin 8) (andIntro ht zeroEqual))
        (argumentsSpecIntro z gamma typ tag payload joinedRest (1 : Fin 8) (andIntro ht zeroEqual))
    ·
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ht hs ha
        exact localFailureIntro H .arguments _ _ _ _ _ _ _ _
          (argumentsSpecIntro z gamma typ tag payload rest (2 : Fin 8) (andIntro ht zeroEqual))
          (argumentsSpecIntro z gamma typ tag payload joinedRest (2 : Fin 8) (andIntro ht zeroEqual))
      ·
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ht hs ha
          exact localFailureIntro H .arguments _ _ _ _ _ _ _ _
            (argumentsSpecIntro z gamma typ tag payload rest (3 : Fin 8) (andIntro ht zeroEqual))
            (argumentsSpecIntro z gamma typ tag payload joinedRest (3 : Fin 8) (andIntro ht zeroEqual))
        ·
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ht hs ha
            exact localFailureIntro H .arguments _ _ _ _ _ _ _ _
              (argumentsSpecIntro z gamma typ tag payload rest (4 : Fin 8) (andIntro ht zeroEqual))
              (argumentsSpecIntro z gamma typ tag payload joinedRest (4 : Fin 8) (andIntro ht zeroEqual))
          ·
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ht hs ha
              exact localFailureIntro H .arguments _ _ _ _ _ _ _ _
                (argumentsSpecIntro z gamma typ tag payload rest (5 : Fin 8) (andIntro ht zeroEqual))
                (argumentsSpecIntro z gamma typ tag payload joinedRest (5 : Fin 8) (andIntro ht zeroEqual))
            ·
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ht hs ha
                apply mapCoupling H .nil .arguments mode gamma typ tag payload rest joinedRest suffix
                  (nilCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
                intro beta j Theta next tail hj hn
                have ht' := renameInto ht j Theta hj
                simp only [equalRename,numeralRelabelAll] at ht'
                exact argumentsSpecIntro next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
                  (payload.relabel j) tail (6 : Fin 8) (andIntro ht' hn)
              ·
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ht hs ha
                  apply mapCoupling H .cons .arguments mode gamma typ tag payload rest joinedRest suffix
                    (consCoupling H out mode gamma typ tag payload rest joinedRest suffix hs ha)
                  intro beta j Theta next tail hj hn
                  have ht' := renameInto ht j Theta hj
                  simp only [equalRename,numeralRelabelAll] at ht'
                  exact argumentsSpecIntro next (gamma.relabel j) (typ.relabel j) (tag.relabel j)
                    (payload.relabel j) tail (7 : Fin 8) (andIntro ht' hn)
                ·
                  exact Fin.elim0 i

theorem argumentsCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepArgumentsDispatch out gamma typ tag payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .arguments mode gamma typ tag payload rest joinedRest suffix)) := by
  apply argumentsSpecCases out gamma typ tag payload rest _ h
  · intro i Theta inc fields
    exact argumentsKnownCoupling H out mode gamma typ tag payload rest joinedRest suffix i
      (andLeft fields) (andRight fields) (weakenProof ha inc)
  · intro Theta inc fields
    exact localFailureIntro H .arguments _ _ _ _ _ _ _ _
      (argumentsSpecFallback z gamma typ tag payload rest (andIntro (andLeft fields) zeroEqual))
      (argumentsSpecFallback z gamma typ tag payload joinedRest (andIntro (andLeft fields) zeroEqual))

/-- Exhaust the actual request mode, retaining malformed-mode rejection. -/
theorem modeCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepModeDispatch H out mode gamma typ tag payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .modes mode gamma typ tag payload rest joinedRest suffix)) := by
  apply choiceCases h
  · intro Theta inc fields
    apply mapCoupling H .terms .modes mode gamma typ tag payload rest joinedRest suffix
      (termCoupling H out mode gamma typ tag payload rest joinedRest suffix (andRight fields) (weakenProof ha inc))
    intro beta j Xi next tail hj hn
    have hm := renameInto (andLeft fields) j Xi hj
    simp only [equalRename,numeral,zRelabel] at hm
    exact orProofLeft (andIntro hm hn)
  · intro Theta inc alternatives
    apply choiceCases alternatives
    · intro Xi inc' fields
      apply mapCoupling H .arguments .modes mode gamma typ tag payload rest joinedRest suffix
        (argumentsCoupling H out mode gamma typ tag payload rest joinedRest suffix
          (andRight fields) (weakenProof (weakenProof ha inc) inc'))
      intro beta j Omega next tail hj hn
      have hm := renameInto (andLeft fields) j Omega hj
      simp only [equalRename,numeral,sucRelabel,zRelabel] at hm
      exact orProofRight (orProofLeft (andIntro hm hn))
    · intro Xi inc' fields
      exact localFailureIntro H .modes _ _ _ _ _ _ _ _
        (orProofRight (orProofRight (andIntro (andLeft fields) zeroEqual)))
        (orProofRight (orProofRight (andIntro (andLeft fields) zeroEqual)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingDispatchProof
