module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data selectedTyped validity)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andRight)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem impApply {P Q : Formula alpha}
    (h : Nonempty (Derivation body Delta (P.imp Q)))
    (hp : Nonempty (Derivation body Delta P)) : Nonempty (Derivation body Delta Q) := by
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination h hp⟩

/-- The actual canonical fold itself supplies output validity, type and
transition fixedness. Only membership is carried through the context slice. -/
theorem foldTyped (data : Data) (out input typ parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (validity data) (numeral 1) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
    (hm : Nonempty (Derivation body Delta (graph2 data.member (numeral 1) typ parameter)))
    (hn : Nonempty (Derivation body Delta (foldGraph data out input parameter))) :
    Nonempty (Derivation body Delta (graph3 (selectedTyped data) (numeral 1) out typ parameter)) := by
  have h := InternalParameterizedCanonicalResultFoldConsumerProof.actualParameterizedCanonicalFoldTypedOutput
    body data alpha Delta out input typ parameter
  exact andRight (impApply (impApply (impApply h (andIntro hv hl)) hm) hn)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportFoldProof
