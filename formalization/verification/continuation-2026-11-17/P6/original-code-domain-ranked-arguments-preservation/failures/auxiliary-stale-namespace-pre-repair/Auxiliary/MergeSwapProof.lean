module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumSwapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeBaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeSwapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open Continuation20261115.BoundsRecombination (merge maximum)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atComponents (left right ls ll rs rl label out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing left ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing right rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum label ll rl)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out
      (OrdinaryArithmetic.addTerm ls rs) label))) :
    Nonempty (Derivation body Delta (graph2 merge out right left)) := by
  have hp := headTransport InternalPairing.pairing out
    (OrdinaryArithmetic.addTerm ls rs) (OrdinaryArithmetic.addTerm rs ls) (Fin.cons label Fin.elim0)
    ⟨InternalAdditionCancellationProof.commutativity ls rs⟩ ho
  exact MergeBaseProof.mergeValue right left rs rl ls ll label out hr hl
    (MaximumSwapProof.swap ll rl label hm) hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeSwapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeSwapProof
