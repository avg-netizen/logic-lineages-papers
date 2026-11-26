module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargetLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open OriginalTransparentLambdaValidityInternal (TagIs BooleanOutput LambdaShape)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof
open OriginalTransparentLambdaValidityInternalLambdaNodeProof
open OriginalTransparentLambdaFinal OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaFinalChildTransportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Transport the independent LOCAL HT recurrence through the internally
proved graph collapse. Both root and actual body call the SAME final target. -/
theorem targetOutput (rawData selected : Data) (ht : TargetCollapse rawData selected)
    (out raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (InternalOriginalUniformDescentSelection.targetValidity selected)
          out raw parameter).iff
        (BooleanOutput out (FinalTargetLambdaFactors selected raw parameter)))) := by
  let N := normalizedData rawData
  let HT := targetValidator rawData
  let T := InternalOriginalUniformDescentSelection.targetValidity selected
  have hlocal : Nonempty (Derivation body Gamma
      ((graph2 HT out raw parameter).iff
        (BooleanOutput out (LambdaShape raw ⊓ FinalLambdaChild HT raw parameter)))) :=
    lambdaOutputEquation (targetRoot N) (InternalLessThan.constantOne 2)
      (InternalLessThan.constantOne 2) out raw parameter (LambdaShape raw) htag
      (targetNodeEquation N raw parameter htag)
  have hchild := childIff (Gamma := Gamma) T HT raw parameter
    (fun beta Delta child childParameterCode => ht body beta Delta (numeral 1) child childParameterCode)
  exact iffCompose (ht body alpha Gamma out raw parameter)
    (iffCompose hlocal (booleanIff out (andIff (iffSelf _) (iffReverse hchild))))

theorem targetLambdaLaw (rawData selected : Data) (ht : TargetCollapse rawData selected) :
    TargetLambdaLaw selected := by
  intro body alpha Delta out raw parameter
  obtain ⟨h⟩ := targetOutput (body := body) (Gamma := TagIs 1 raw :: Delta)
    rawData selected ht out raw parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargetLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargetLambdaProof
