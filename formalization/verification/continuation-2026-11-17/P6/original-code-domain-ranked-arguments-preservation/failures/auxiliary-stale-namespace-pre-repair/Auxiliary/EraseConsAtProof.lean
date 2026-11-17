module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseRemoveBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepBranchesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseInvariantBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseConsAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open EraseInvariant
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroBit (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (hf : Nonempty (Derivation body Delta (countEffect tail needle rest z)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (result list needle bit remaining)) := by
  apply formulaCases (eqn head needle)
  · exact EraseRemoveBranchProof.remove list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hf _) (withHyp ha _) (withHyp hap _)
  · exact EraseKeepBranchesProof.absent list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hf _) (withHyp ha _) (withHyp hap _)

theorem atTail (list head tail needle acc childBit rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc childBit rest)))
    (hf : Nonempty (Derivation body Delta (result tail needle childBit rest)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (result list needle bit remaining)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases (andLeft hf)
  · have he : Nonempty (Derivation body ((eqn childBit z) :: Delta) (eqn childBit z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp0 := headTransport InternalPairing.pairing acc childBit z (Fin.cons rest Fin.elim0) he (withHyp hp _)
    have hf0 := EraseResultTransportProof.bitTransport tail needle childBit z rest he (withHyp hf _)
    exact zeroBit list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) hp0 (andRight hf0) (withHyp ha _) (withHyp hap _)
  · have he : Nonempty (Derivation body ((eqn childBit (suc z)) :: Delta) (eqn childBit (suc z))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp1 := headTransport InternalPairing.pairing acc childBit (suc z) (Fin.cons rest Fin.elim0) he (withHyp hp _)
    have hf1 := EraseResultTransportProof.bitTransport tail needle childBit (suc z) rest he (withHyp hf _)
    exact EraseKeepBranchesProof.found list head tail needle acc rest actual bit remaining
      (withHyp hc _) (withHyp ht _) hp1 (andRight hf1) (withHyp ha _) (withHyp hap _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseConsAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseConsAtProof
