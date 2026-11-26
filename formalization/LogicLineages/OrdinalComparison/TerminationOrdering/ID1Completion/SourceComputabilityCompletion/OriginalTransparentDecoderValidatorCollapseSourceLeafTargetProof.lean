module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafTargetProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaValidityInternalBranchSupportProof
open OriginalTransparentLambdaValidityInternalBranchValueProof
open OriginalTransparentDecoderValidatorCollapseSourceLeafProof
open InternalOriginalUniformDescentSelection (Data)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem targetOpaqueAcceptance (data : Data) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator (targetRoot data) (InternalLessThan.constantOne 2)
          (InternalLessThan.constantOne 2)) (numeral 1) raw parameter).iff
        (graph2 data.oldTarget (numeral 1) raw parameter))) := by
  let A := graph2 (validator (targetRoot data) (InternalLessThan.constantOne 2)
    (InternalLessThan.constantOne 2)) (numeral 1) raw parameter
  let B := graph2 data.oldTarget (numeral 1) raw parameter
  have he := popAcceptanceEquation (targetRoot data) (InternalLessThan.constantOne 2)
    (InternalLessThan.constantOne 2) raw parameter h2 h1
  have hf : Nonempty (Derivation body (A :: Gamma) B) := by
    obtain ⟨he'⟩ := addAssumption he A
    have factors : Nonempty (Derivation body (A :: Gamma)
        (graph2 (targetRoot data) (numeral 1) raw parameter ⊓
          graph2 (InternalLessThan.constantOne 2) (numeral 1) raw parameter)) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft he') (Derivation.hypothesis List.mem_cons_self)⟩
    exact dispatchOpaque data.oldTarget lambdaShape (numeral 1) raw parameter
      (addAssumption h2 A) (addAssumption h1 A) (andLeft factors)
  have hb : Nonempty (Derivation body (B :: Gamma) A) := by
    have ht := dispatchOpaqueValue data.oldTarget lambdaShape (numeral 1) raw parameter
      (addAssumption h2 B) (addAssumption h1 B)
      (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hparts⟩ := andIntro ht
      (InternalLessThanSupportProof.oneConstantValue (Fin.cons raw (Fin.cons parameter Fin.elim0)))
    obtain ⟨he'⟩ := addAssumption he B
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight he') hparts⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafTargetProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLeafTargetProof
