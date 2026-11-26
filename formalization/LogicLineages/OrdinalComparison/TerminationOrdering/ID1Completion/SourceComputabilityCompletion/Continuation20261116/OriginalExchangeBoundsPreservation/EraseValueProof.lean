module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant sameOf)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Erase
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem flagValue (head acc needle bit tail : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit tail))) :
    Nonempty (Derivation body Delta (graph3 flag bit head acc needle)) :=
  unaryValue InternalUnpair.left (.projection 1) bit acc ![head,acc,needle]
    (pairLeft acc bit tail hp) (projectionValue 1 ![head,acc,needle])

theorem restValue (head acc needle bit tail : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit tail))) :
    Nonempty (Derivation body Delta (graph3 rest tail head acc needle)) :=
  unaryValue InternalUnpair.right (.projection 1) tail acc ![head,acc,needle]
    (pairRight acc bit tail hp) (projectionValue 1 ![head,acc,needle])

theorem keptValue (head acc needle bit tail code : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit tail)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail))) :
    Nonempty (Derivation body Delta (graph3 kept code head acc needle)) :=
  binaryValue InternalListCodec.consCode (.projection 0) rest code head tail ![head,acc,needle]
    hc (projectionValue 0 ![head,acc,needle]) (restValue head acc needle bit tail hp)

theorem removeValue (head acc needle tail out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z tail)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) tail)))
    (he : Nonempty (Derivation body Delta (eqn head needle))) :
    Nonempty (Derivation body Delta (graph3 step out head acc needle)) := by
  have hf := binaryValue InternalPairing.pairing (constant 3 1) rest out (numeral 1) tail ![head,acc,needle]
    ho (constantValue 1 ![head,acc,needle]) (restValue head acc needle z tail hp)
  have hb := successorBranchIntro (sameOf (.projection 0) (.projection 2)) keepAbsent found out z ![head,acc,needle]
    (Continuation20261114.ArgumentEntryCount.InternalProof.queryEqual head acc needle he) hf
  exact zeroBranchIntro flag
    (InternalAcceptance.branch (sameOf (.projection 0) (.projection 2)) keepAbsent found)
    keepFound out ![head,acc,needle] (flagValue head acc needle z tail hp) hb

theorem nil (needle : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 state z z needle)) :=
  InternalRawListRecursionProof.nilValue (constant 1 0) step z (Fin.cons needle Fin.elim0)
    (constantValue 0 (Fin.cons needle Fin.elim0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseValueProof
