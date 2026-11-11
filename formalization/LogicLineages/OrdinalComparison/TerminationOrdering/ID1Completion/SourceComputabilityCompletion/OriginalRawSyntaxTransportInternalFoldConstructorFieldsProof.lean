module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineExpansionProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaFields (raw k domain body : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph2 lambdaConstructor raw domain body))) :
    Nonempty (Derivation positive Delta (UnaryFields raw k body (suc k))) := by
  let xs : Fin 2 → OTerm alpha := ![k,raw]
  have htag := lambdaTag (.projection 1) raw domain body xs (projectionValue 1 xs) hc
  have hk : Nonempty (Derivation positive Delta (graph2 nextCutoff (suc k) k raw)) := by
    apply branchNumeralIntro 1 1 (leftOf (.projection 1)) _ _ (suc k) xs htag
    exact unaryValue .succ (.projection 0) (suc k) k xs (successorValue ![k]) (projectionValue 0 xs)
  exact andIntro (lambdaArity (.projection 0) raw domain body ![raw] (projectionValue 0 ![raw]) hc)
    (andIntro (lambdaFirst (.projection 0) raw domain body ![raw] (projectionValue 0 ![raw]) hc) hk)

theorem ordinaryFields (raw k head base : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph2 ordinaryConstructor raw head base))) :
    Nonempty (Derivation positive Delta (UnaryFields raw k base (k))) := by
  let xs : Fin 2 → OTerm alpha := ![k,raw]
  have htag := ordinaryTag (.projection 1) raw head base xs (projectionValue 1 xs) hc
  have hk : Nonempty (Derivation positive Delta (graph2 nextCutoff (k) k raw)) := by
    apply branchNumeralIntro 4 1 (leftOf (.projection 1)) _ _ (k) xs htag
    exact projectionValue 0 xs
  exact andIntro (ordinaryArity (.projection 0) raw head base ![raw] (projectionValue 0 ![raw]) hc)
    (andIntro (ordinaryFirst (.projection 0) raw head base ![raw] (projectionValue 0 ![raw]) hc) hk)

theorem applicationFields (raw domain fn arg : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph3 applicationConstructor raw domain fn arg))) :
    Nonempty (Derivation positive Delta (BinaryFields raw fn arg)) :=
  andIntro (applicationArity (.projection 0) raw domain fn arg ![raw] (projectionValue 0 ![raw]) hc)
    (andIntro (applicationFirst (.projection 0) raw domain fn arg ![raw] (projectionValue 0 ![raw]) hc)
      (applicationSecond (.projection 0) raw domain fn arg ![raw] (projectionValue 0 ![raw]) hc))

theorem consFields (raw tau head tail : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph3 consConstructor raw tau head tail))) :
    Nonempty (Derivation positive Delta (BinaryFields raw head tail)) :=
  andIntro (consArity (.projection 0) raw tau head tail ![raw] (projectionValue 0 ![raw]) hc)
    (andIntro (consFirst (.projection 0) raw tau head tail ![raw] (projectionValue 0 ![raw]) hc)
      (consSecond (.projection 0) raw tau head tail ![raw] (projectionValue 0 ![raw]) hc))

theorem numberedFields (raw label head tau base types extras : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras]))) :
    Nonempty (Derivation positive Delta (BinaryFields raw base extras)) :=
  andIntro (numberedArity (.projection 0) raw label head tau base types extras ![raw] (projectionValue 0 ![raw]) hc)
    (andIntro (numberedFirst (.projection 0) raw label head tau base types extras ![raw] (projectionValue 0 ![raw]) hc)
      (numberedSecond (.projection 0) raw label head tau base types extras ![raw] (projectionValue 0 ![raw]) hc))


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
