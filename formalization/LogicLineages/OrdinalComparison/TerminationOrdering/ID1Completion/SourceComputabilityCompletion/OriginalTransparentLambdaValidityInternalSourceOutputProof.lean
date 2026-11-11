module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalSourceCheckProof OriginalTransparentLambdaValidityInternalBooleanProof
open OriginalTransparentLambdaValidityInternalBranchSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InternalOriginalUniformDescentSelection (Data)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem sourceCheckReject (data : Data) (raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter).not)) :
    Nonempty (Derivation body Gamma (graph2 (sourceCheck data) z raw parameter)) := by
  obtain ⟨hn⟩ := hn
  let A := graph2 (sourceCheck data) (numeral 1) raw parameter
  obtain ⟨hs⟩ := sourceCheckRecover data raw parameter
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hna : Nonempty (Derivation body Gamma A.not) :=
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hn A) hs)⟩
  exact conjunctionReject _ _ ![raw,parameter] hna

theorem sourceCheckEquation (data : Data) (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (sourceCheck data) out raw parameter).iff
        (BooleanOutput out (SourceLambdaRootFactors data raw parameter)))) := by
  let S := SourceLambdaRootFactors data raw parameter
  obtain ⟨hy⟩ := sourceCheckValue (body := body) (Gamma := S :: Gamma) data raw parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := sourceCheckReject (body := body) (Gamma := S.not :: Gamma) data raw parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact booleanEquation (sourceCheck data) ![raw,parameter] out S
    ⟨Derivation.implicationIntroduction hy⟩ ⟨Derivation.implicationIntroduction hn⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceOutputProof
