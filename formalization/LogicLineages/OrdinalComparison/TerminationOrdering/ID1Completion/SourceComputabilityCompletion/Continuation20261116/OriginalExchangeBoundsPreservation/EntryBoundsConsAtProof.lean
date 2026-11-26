module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z suc)
open Continuation20261115

theorem cons (n : Nat) (raw typ head tail hv hs hl tv ts tl label out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hh : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) hv head)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) tv tail)))
    (hph : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing hv hs hl)))
    (hpt : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tv ts tl)))
    (hmax : Nonempty (Derivation body Delta (graph2 maximum label hl tl)))
    (hm : Nonempty (Derivation body Delta (graph2 merge out hv tv))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) out raw)) := by
  have hp := MergeRecoverProof.pairAtMaximum hv tv hs hl ts tl label out hph hpt hmax hm
  exact OriginalCodeBoundsConstructors.BinaryValueProof.value true n raw typ head tail hv hs hl tv ts tl label out
    hc hg hh ht hph hpt hmax hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsAtProof
