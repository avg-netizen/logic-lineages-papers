module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineRecoveryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalEnumerationRecursionInterface
open InternalAcceptanceSupportProof
open InternalListCodecSupportProof InternalRawListRecursionSupportProof
theorem positive (n : Nat) (node param bound fuel ts hs ls tb p2 p3 prior opened tail answers out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound (suc fuel))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail opened z)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode answers prior tail)))
    (hv1 : Nonempty (Derivation body Delta (Lists.AllValid n prior)))
    (hv2 : Nonempty (Derivation body Delta (Lists.AllValid n opened)))
    (hg : Nonempty (Derivation body Delta (graph3 (G n) (suc out) node answers param))) :
    Nonempty (Derivation body Delta (Lists.AllValid n out)) := by
  have hl0 := OriginalAllPositionContextDeleteBaseProof.lookupZero answers prior tail ha
  have hl1 := lookupValue opened (suc z) answers tail
    (OriginalAllPositionContextDeleteBaseProof.dropOne answers prior tail ha) (consHead tail opened z ht)
  have hpos := CombineRecoveryProof.positive n node answers param fuel out
    (SelectorProof.fuelAt node answers param bound (suc fuel) hn) hg
  have hlayer := CombineScalarProof.layerRecover n node answers param bound (suc fuel) ts hs ls tb p2 p3
    prior opened out hn hp h2 h3 hl0 hl1 hpos
  exact ListClosureProof.layer n ![ts,hs,ls,tb,bound,prior,opened] out hv1 hv2 hlayer
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineClosureProof
