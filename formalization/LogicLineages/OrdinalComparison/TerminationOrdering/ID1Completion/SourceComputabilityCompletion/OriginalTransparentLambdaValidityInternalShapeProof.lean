module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalShapeAcceptanceProof OriginalTransparentLambdaValidityInternalBooleanProof
open InternalTagArithmeticSyntaxProof (z)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem shapeReject (raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (LambdaShape raw).not)) :
    Nonempty (Derivation body Gamma (graph2 lambdaShape z raw parameter)) := by
  obtain ⟨hn⟩ := hn
  let A := graph2 lambdaShape (numeral 1) raw parameter
  obtain ⟨hs⟩ := shapeRecover raw parameter
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hna : Nonempty (Derivation body Gamma A.not) :=
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hn A) hs)⟩
  exact sameReject resultType (consOf domain codomain) ![raw,parameter] hna

theorem actualOriginalTransparentInternalShape :
    OriginalTransparentLambdaValidityInternalTargets.ActualOriginalTransparentInternalShape := by
  intro body alpha out raw parameter
  obtain ⟨hy⟩ := shapeValue (body := body) (Gamma := [LambdaShape raw]) raw parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := shapeReject (body := body) (Gamma := [(LambdaShape raw).not]) raw parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact booleanEquation lambdaShape ![raw,parameter] out (LambdaShape raw)
    ⟨Derivation.implicationIntroduction hy⟩ ⟨Derivation.implicationIntroduction hn⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeProof
