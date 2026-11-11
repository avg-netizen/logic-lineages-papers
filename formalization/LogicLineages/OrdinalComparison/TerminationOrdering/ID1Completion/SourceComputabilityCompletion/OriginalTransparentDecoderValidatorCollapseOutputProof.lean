module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open OriginalTransparentDecoderValidatorCollapse
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open OriginalTransparentLambdaValidityInternal (BooleanOutput)
open OriginalTransparentLambdaValidityInternalBooleanProof (booleanEquation)
open OriginalTransparentLambdaValidityInternalBranchSupportProof (conjunctionReject)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalHereditaryValidityInternalRecurrenceOutputSupportProof (validatorReject)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTypedDecoderTransportLogicalProof
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Independent exact zero rejection plus original functionality determines
all validator outputs from its own graph-at-one formula. -/
theorem validatorBooleanEquation (s t m : Program 2) (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) out raw parameter).iff
        (BooleanOutput out (graph2 (validator s t m) (numeral 1) raw parameter)))) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  obtain ⟨hn⟩ := validatorReject (body := body) (Gamma := A.not :: Gamma) s t m raw parameter
    (show Nonempty (Derivation body (A.not :: Gamma) A.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact booleanEquation (validator s t m) ![raw,parameter] out A
    ⟨Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.implicationIntroduction hn⟩

theorem conjunctionBooleanEquation (p q : Program 2) (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (InternalAcceptance.conjunction p q) out raw parameter).iff
        (BooleanOutput out (graph2 (InternalAcceptance.conjunction p q) (numeral 1) raw parameter)))) := by
  let A := graph2 (InternalAcceptance.conjunction p q) (numeral 1) raw parameter
  obtain ⟨hn⟩ := conjunctionReject (body := body) (Gamma := A.not :: Gamma) p q ![raw,parameter]
    (show Nonempty (Derivation body (A.not :: Gamma) A.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact booleanEquation (InternalAcceptance.conjunction p q) ![raw,parameter] out A
    ⟨Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.implicationIntroduction hn⟩

/-- Acceptance equality is promoted only after both actual ASTs have exact
zero/one equations. Neither Boolean output nor rejection is an external premise. -/
theorem validatorConjunctionOutput (s t m p q : Program 2) (out raw parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma
      (Acceptance (validator s t m) (InternalAcceptance.conjunction p q) raw parameter))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) out raw parameter).iff
        (graph2 (InternalAcceptance.conjunction p q) out raw parameter))) :=
  iffCompose (validatorBooleanEquation s t m out raw parameter)
    (iffCompose (booleanIff out he) (iffReverse (conjunctionBooleanEquation p q out raw parameter)))

/-- Final target transport reuses the identical accepted final selection. -/
theorem finalTargetFrom (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (h : TargetCollapse p H G W) : FinalTargetCollapse p H G W := by
  intro body alpha Gamma out raw parameter
  have hf := (OriginalLambdaTraversalSelectionValidityProof.finalInternalLaws (refined p H G W)).1.1
  exact iffCompose (hf body alpha Gamma out raw parameter) (h body alpha Gamma out raw parameter)

/-- The actual final source conjunction is removed internally using the
original guarded source's checked implication into the original target. -/
theorem finalSourceFrom (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (ht : TargetCollapse p H G W) (hs : SourceCollapse p H G W) : FinalSourceCollapse p H G W := by
  intro body alpha Gamma out raw parameter
  let r := refined p H G W
  let q := transparent p H G W
  let T := graph2 (targetValidator r.base) (numeral 1) raw parameter
  let S := graph2 (sourceValidator r.base) (numeral 1) raw parameter
  let Q := graph2 q.base.oldSource (numeral 1) raw parameter
  have hsource := hs body alpha Gamma (numeral 1) raw parameter
  have htarget := ht body alpha Gamma (numeral 1) raw parameter
  have he : Nonempty (Derivation body Gamma ((T ⊓ S).iff Q)) := by
    have forward : Nonempty (Derivation body (T ⊓ S :: Gamma) Q) :=
      iffForward (addAssumption hsource (T ⊓ S))
        (andRight (show Nonempty (Derivation body (T ⊓ S :: Gamma) (T ⊓ S)) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩))
    have backward : Nonempty (Derivation body (Q :: Gamma) (T ⊓ S)) := by
      have hq : Nonempty (Derivation body (Q :: Gamma) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hqt := OriginalTransparentDecoderValidatorCollapsePackedImplicationProof.sourceToTarget H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W raw parameter hq
      exact andIntro (iffBackward (addAssumption htarget Q) hqt)
        (iffBackward (addAssumption hsource Q) hq)
    obtain ⟨forward⟩ := forward
    obtain ⟨backward⟩ := backward
    exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
      (Derivation.implicationIntroduction backward)⟩
  have hfinal := (OriginalLambdaTraversalSelectionValidityProof.finalInternalLaws r).1.2.2
  have hconj := conjunctionEquation (body := body) (Gamma := Gamma) (targetValidator r.base) (sourceValidator r.base)
    ![raw,parameter] out
  have hq := conjunctionBooleanEquation (body := body) (Gamma := Gamma)
    (.composition G ![leftOf (.projection 1)])
    (.composition (OriginalUniverseDecoder.termCheck H
      (InternalOriginalUniformContextMembership.contextMember p.base.member) W)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1),leftOf (.projection 1)])
    out raw parameter
  exact iffCompose (hfinal body alpha Gamma out raw parameter)
    (iffCompose hconj (iffCompose (booleanIff out he) (iffReverse hq)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOutputProof
