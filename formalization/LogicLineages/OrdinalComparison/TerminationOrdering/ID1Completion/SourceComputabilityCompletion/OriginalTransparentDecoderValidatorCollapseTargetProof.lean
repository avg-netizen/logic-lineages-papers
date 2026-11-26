module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetLambdaInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafNormalizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTransparentDecoderValidatorCollapse OriginalTransparentDecoderValidatorCollapseTargets
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseInductionProof
open OriginalTransparentDecoderValidatorCollapseTargetApplicationInductionProof
open OriginalTransparentDecoderValidatorCollapseTargetLambdaInductionProof
open OriginalTransparentDecoderValidatorCollapseSourceLeafNormalizationProof
open OriginalTransparentDecoderValidatorCollapseOutputProof
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open OriginalTransparentLambdaValidityInternal (TagIs)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Exhaustive local target step over all raw tags, including malformed input. -/
theorem targetStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (payload raw parameter : OTerm alpha)
    (hind : Nonempty (Derivation body Gamma
      (belowPayload (targetValidator (refined p H G W).base) (transparent p H G W).base.oldTarget payload)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Gamma
      (Acceptance (targetValidator (refined p H G W).base) (transparent p H G W).base.oldTarget raw parameter)) := by
  let A := TagIs 2 raw
  apply formulaCases A
  · exact applicationByInduction (refined p H G W).base H G payload raw parameter
      (addAssumption hind A) (addAssumption hp A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · let B := TagIs 1 raw
    apply formulaCases B
    · exact lambdaByInduction (refined p H G W).base H G payload raw parameter
        (addAssumption (addAssumption hind A.not) B) (addAssumption (addAssumption hp A.not) B)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    · exact targetLeafEquality p H G W raw parameter
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩

/-- Independent all-raw HT acceptance equality by original-payload induction.
No calibration, typed input, accepted child or internal reflection is assumed. -/
theorem targetAcceptance (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      (Acceptance (targetValidator (refined p H G W).base) (transparent p H G W).base.oldTarget raw parameter)) :=
  acceptanceInduction _ _ (fun _ _ payload input parameter hind hp =>
    targetStep p H G W payload input parameter hind hp) raw parameter

theorem actualOriginalTransparentDecoderTargetCollapse : ActualOriginalTransparentDecoderTargetCollapse := by
  intro p H G W body alpha Gamma out raw parameter
  let N := normalizedData (refined p H G W).base
  exact validatorConjunctionOutput (targetRoot N) (InternalLessThan.constantOne 2)
    (InternalLessThan.constantOne 2)
    (.composition G (fun _ : Fin 1 => leftOf (.projection 1)))
    (.composition (OriginalTypedDecoder.termCheck H)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)])
    out raw parameter (targetAcceptance p H G W raw parameter)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargetProof
