module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.FieldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tagValue (numbered : Bool) (raw k f tau base ts extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (Targets.constructor numbered raw k f tau base ts extras))) :
    Nonempty (Derivation body Delta
      (graph1 (leftOf (.projection 0)) (numeral (if numbered then 5 else 4)) raw)) := by
  have hq : Nonempty (Derivation body Delta (graph1 (.projection 0) raw raw)) := projectionValue 0 ![raw]
  cases numbered with
  | false => exact ordinaryTag (.projection 0) raw f base ![raw] hq hc
  | true => exact numberedTag (.projection 0) raw k f tau base ts extras ![raw] hq hc

theorem headValue (numbered : Bool) (raw k f tau base ts extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (Targets.constructor numbered raw k f tau base ts extras))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) f raw)) := by
  have hq : Nonempty (Derivation body Delta (graph1 (.projection 0) raw raw)) := projectionValue 0 ![raw]
  have ht := tagValue numbered raw k f tau base ts extras hc
  cases numbered with
  | false =>
    exact branchNumeralIntro 4 5 (leftOf (.projection 0))
      (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf (.projection 0)))) f ![raw] ht
      (ordinaryHead (.projection 0) raw f base ![raw] hq hc)
  | true =>
    exact branchNumeralIntro 5 5 (leftOf (.projection 0))
      (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf (.projection 0)))) f ![raw] ht
      (numberedHead (.projection 0) raw k f tau base ts extras ![raw] hq hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.FieldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.FieldProof
