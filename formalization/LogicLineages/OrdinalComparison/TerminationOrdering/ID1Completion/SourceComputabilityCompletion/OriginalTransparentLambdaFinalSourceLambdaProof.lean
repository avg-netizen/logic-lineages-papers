module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceFactorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open OriginalTransparentLambdaValidityInternal (TagIs BooleanOutput LambdaShape SourceLambdaRootFactors)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof
open OriginalTransparentLambdaValidityInternalLambdaNodeProof
open OriginalTransparentLambdaFinal OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaFinalChildTransportProof
open OriginalTransparentLambdaFinalSourceFactorProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Both LOCAL validator calls decompose independently. Original selector
functionality fuses their child witnesses, then the internally proved source
collapse restores the SAME actual final source at that body's own parameter.
Only the literal member-field identity changes the root formula's Data. -/
theorem sourceFactors (rawData selected : Data) (hs : SourceCollapse rawData selected)
    (hm : selected.member = (normalizedData rawData).member)
    (raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (targetValidator rawData) (numeral 1) raw parameter ⊓
          graph2 (sourceValidator rawData) (numeral 1) raw parameter).iff
        (FinalSourceLambdaFactors selected raw parameter))) := by
  let N := normalizedData rawData
  let HT := targetValidator rawData
  let HS := sourceValidator rawData
  let S := InternalOriginalUniformDescentSelection.validity selected
  have htarget : Nonempty (Derivation body Gamma
      ((graph2 HT (numeral 1) raw parameter).iff
        (LambdaShape raw ⊓ FinalLambdaChild HT raw parameter))) :=
    lambdaAcceptanceEquation (targetRoot N) (InternalLessThan.constantOne 2)
      (InternalLessThan.constantOne 2) raw parameter (LambdaShape raw) htag
      (targetNodeEquation N raw parameter htag)
  have hsource : Nonempty (Derivation body Gamma
      ((graph2 HS (numeral 1) raw parameter).iff
        (SourceLambdaRootFactors N raw parameter ⊓ FinalLambdaChild HS raw parameter))) :=
    lambdaAcceptanceEquation (sourceRoot N) (targetRoot N) N.member
      raw parameter (SourceLambdaRootFactors N raw parameter) htag
      (sourceNodeEquation N raw parameter htag)
  have hmerged := iffCompose (andIff htarget hsource)
    (iffCompose (mergeFactors N raw parameter
      (FinalLambdaChild HT raw parameter) (FinalLambdaChild HS raw parameter))
      (andIff (iffSelf _) (iffReverse (childConjunction HT HS raw parameter))))
  rw [sourceRootMemberIdentity N selected hm.symm raw parameter] at hmerged
  have hchild := childIff (Gamma := Gamma) S (InternalAcceptance.conjunction HT HS) raw parameter
    (fun beta Delta child childParameterCode => hs body beta Delta (numeral 1) child childParameterCode)
  exact iffCompose hmerged (andIff (iffSelf _) (iffReverse hchild))

/-- Full rejection and reconstruction, not just accepted-input descent.
All outer/domain memberships and actual final body acceptance are conclusion
factors. The SAME final source is never replaced by the transparent helper. -/
theorem sourceOutput (rawData selected : Data) (hs : SourceCollapse rawData selected)
    (hm : selected.member = (normalizedData rawData).member)
    (out raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (InternalOriginalUniformDescentSelection.validity selected)
          out raw parameter).iff
        (BooleanOutput out (FinalSourceLambdaFactors selected raw parameter)))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  exact iffCompose (hs body alpha Gamma out raw parameter)
    (iffCompose (conjunctionEquation (targetValidator rawData) (sourceValidator rawData) xs out)
      (booleanIff out (sourceFactors rawData selected hs hm raw parameter htag)))

theorem sourceLambdaLaw (rawData selected : Data) (hs : SourceCollapse rawData selected)
    (hm : selected.member = (normalizedData rawData).member) :
    SourceLambdaLaw selected := by
  intro body alpha Delta out raw parameter
  obtain ⟨h⟩ := sourceOutput (body := body) (Gamma := TagIs 1 raw :: Delta)
    rawData selected hs hm out raw parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceLambdaProof
