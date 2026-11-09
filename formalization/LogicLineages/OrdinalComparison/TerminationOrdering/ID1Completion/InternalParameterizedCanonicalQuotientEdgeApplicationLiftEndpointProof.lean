module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEndpointProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data validity)
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalParameterizedCanonicalQuotientEdgeApplicationLiftSyntaxProof
open InternalParameterizedCanonicalResultFold (foldGraph)
open InternalParameterizedCanonicalResultFoldSyntaxProof (foldGraphRename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The actual fold output identifies the raw source's type. No old
representative tag or semantic decoding theorem is assumed internally. -/
theorem rawSourceWithTag (data : Data) (out input typ tag parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data out typ parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity data) InternalOriginalStepGuard.one input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag input))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)) := by
  have hc := InternalParameterizedCanonicalResultFoldConsumerProof.certifiedAt
    data out input tag parameter hv hl hn
  have ho := andRight hc
  have htout := InternalParameterizedQuotientEdgeCheckerTypedProof.typedSourceTag
    data out typ parameter ht
  have he := valueUnique InternalUnpair.left tag typ (Fin.cons out Fin.elim0)
    (andLeft (andRight ho)) htout
  exact outputTransport InternalUnpair.left tag typ (Fin.cons input Fin.elim0) he hl

theorem rawSourceTag (data : Data) (out input typ parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data out typ parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity data) InternalOriginalStepGuard.one input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)) := by
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro β j Delta tag hj hl
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hl
  have ht' := renameInto ht j Delta hj
  rw [typedAcceptedRename] at ht'
  have hv' := renameInto hv j Delta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv'
  have hn' := renameInto hn j Delta hj
  rw [foldGraphRename] at hn'
  exact rawSourceWithTag data (out.relabel j) (input.relabel j) (typ.relabel j)
    tag (parameter.relabel j) ht' hv' hn' hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEndpointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEndpointProof
