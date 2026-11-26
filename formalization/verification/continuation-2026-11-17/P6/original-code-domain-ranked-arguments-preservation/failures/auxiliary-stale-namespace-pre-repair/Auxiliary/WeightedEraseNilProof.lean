module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseEffectProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedErase
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (symm)

theorem nil (weight : Program 1) (needle acc bit rest total remainingWeight needleWeight : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc z needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total z)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingWeight rest))) :
    Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight)) := by
  have he := valueUnique Erase.state z acc ![z,needle] (EraseValueProof.nil needle) hv
  have hpa := outputTransport InternalPairing.pairing z acc ![z,z] he
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  have hb := valueUnique InternalUnpair.left z bit ![acc]
    (pairLeft acc z z hpa) (pairLeft acc bit rest hp)
  have hrs := valueUnique InternalUnpair.right z rest ![acc]
    (pairRight acc z z hpa) (pairRight acc bit rest hp)
  obtain ⟨hrs'⟩ := hrs
  have hr0 := headTransport (Fold.weighted weight) remainingWeight rest z Fin.elim0 ⟨symm hrs'⟩ hr
  have hs := valueUnique (Fold.weighted weight) total remainingWeight ![z] ht hr0
  exact WeightedEraseTransportProof.bitTransport z total remainingWeight needleWeight bit hb
    (WeightedEraseEffectProof.absent total remainingWeight needleWeight hs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseNilProof
