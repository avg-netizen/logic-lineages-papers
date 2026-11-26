module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseBranchAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseInvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceBranchAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EraseAbsence
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andRight)
open Continuation20261114
theorem remove (list head tail needle acc rest out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) rest))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (result list needle (suc z))) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseValueProof.removeValue head acc needle rest out hp ho he)
  · exact EraseAbsenceResultProof.one list needle

theorem absent (list head tail needle acc rest kept out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle).not))
    (hf : Nonempty (Derivation body Delta (result tail needle z)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z kept))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (result list needle z)) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseKeepProof.absent head acc needle rest kept out hp hk ho he)
  · exact EraseAbsenceResultProof.zero list needle
      (ArgumentEntryCount.InternalProof.internalUnequalCons body alpha Delta list head tail needle z hc
        (EraseAbsenceResultProof.zeroCount tail needle hf) he)

theorem found (list head tail needle acc rest kept out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (suc z) rest)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) kept))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (result list needle (suc z))) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseKeepProof.alreadyFound head acc needle rest kept out hp hk ho)
  · exact EraseAbsenceResultProof.one list needle

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceBranchAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceBranchAtProof
