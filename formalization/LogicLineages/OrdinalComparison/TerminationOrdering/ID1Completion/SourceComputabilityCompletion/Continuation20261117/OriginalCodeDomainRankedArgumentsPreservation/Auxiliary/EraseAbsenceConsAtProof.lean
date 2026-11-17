module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceRemoveBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceKeepBranchesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseInvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceConsAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open EraseAbsence
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroBit (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (hf : Nonempty (Derivation body Delta (result tail needle z)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (result list needle bit)) := by
  apply formulaCases (eqn head needle)
  · exact EraseAbsenceRemoveBranchProof.remove list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp ha _) (withHyp hap _)
  · exact EraseAbsenceKeepBranchesProof.absent list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hf _) (withHyp ha _) (withHyp hap _)

theorem atTail (list head tail needle acc childBit rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc childBit rest)))
    (hf : Nonempty (Derivation body Delta (result tail needle childBit)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (result list needle bit)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases (andLeft (EraseInvariantProof.actualResult tail needle acc childBit rest ht hp))
  · have he : Nonempty (Derivation body ((eqn childBit z) :: Delta) (eqn childBit z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp0 := headTransport InternalPairing.pairing acc childBit z (Fin.cons rest Fin.elim0) he (withHyp hp _)
    have hf0 := EraseAbsenceResultProof.bitTransport tail needle childBit z he (withHyp hf _)
    exact zeroBit list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) hp0 hf0 (withHyp ha _) (withHyp hap _)
  · have he : Nonempty (Derivation body ((eqn childBit (suc z)) :: Delta) (eqn childBit (suc z))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp1 := headTransport InternalPairing.pairing acc childBit (suc z) (Fin.cons rest Fin.elim0) he (withHyp hp _)
    exact EraseAbsenceKeepBranchesProof.found list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) hp1 (withHyp ha _) (withHyp hap _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceConsAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceConsAtProof
