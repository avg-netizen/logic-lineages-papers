module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepProof
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

theorem absent (head acc needle tail code out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z tail)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z code)))
    (he : Nonempty (Derivation body Delta (eqn head needle).not)) :
    Nonempty (Derivation body Delta (graph3 step out head acc needle)) := by
  have hk := binaryValue InternalPairing.pairing (constant 3 0) kept out z code ![head,acc,needle]
    ho (constantValue 0 ![head,acc,needle]) (EraseValueProof.keptValue head acc needle z tail code hp hc)
  have hb := zeroBranchIntro (sameOf (.projection 0) (.projection 2)) keepAbsent found out ![head,acc,needle]
    (Continuation20261114.ArgumentEntryCount.InternalProof.queryUnequal head acc needle he) hk
  exact zeroBranchIntro flag
    (InternalAcceptance.branch (sameOf (.projection 0) (.projection 2)) keepAbsent found)
    keepFound out ![head,acc,needle] (EraseValueProof.flagValue head acc needle z tail hp) hb

theorem alreadyFound (head acc needle tail code out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (numeral 1) tail)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) code))) :
    Nonempty (Derivation body Delta (graph3 step out head acc needle)) := by
  have hk := binaryValue InternalPairing.pairing (constant 3 1) kept out (numeral 1) code ![head,acc,needle]
    ho (constantValue 1 ![head,acc,needle]) (EraseValueProof.keptValue head acc needle (numeral 1) tail code hp hc)
  exact successorBranchIntro flag
    (InternalAcceptance.branch (sameOf (.projection 0) (.projection 2)) keepAbsent found)
    keepFound out z ![head,acc,needle] (EraseValueProof.flagValue head acc needle (numeral 1) tail hp) hk

theorem cons (list head tail needle acc out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state acc tail needle)))
    (hs : Nonempty (Derivation body Delta (graph3 step out head acc needle))) :
    Nonempty (Derivation body Delta (graph2 state out list needle)) :=
  InternalRawListRecursionProof.consValue (constant 1 0) step list head tail acc out
    (Fin.cons needle Fin.elim0) hc ht hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepProof
