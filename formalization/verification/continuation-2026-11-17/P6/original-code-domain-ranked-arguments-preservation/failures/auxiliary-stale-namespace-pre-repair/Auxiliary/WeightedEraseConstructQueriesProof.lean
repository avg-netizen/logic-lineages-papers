module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseConstructQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseConstructQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EraseConstructQueriesProof (kept paired)
def folded (weight : Program 1) : Program 3 := .composition (Fold.weighted weight) (fun _ : Fin 1 => kept)
def queries (weight : Program 1) : Fin 3 → Program 3 := ![kept,paired,folded weight]

theorem recover (weight : Program 1) (bit head rest : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries weight i) (ys i) ![bit,head,rest]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (ys 0) head rest)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 1) bit (ys 0))) ∧
    Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) (ys 2) (ys 0))) := by
  have hk := binaryRecover InternalListCodec.consCode (.projection 1) (.projection 2) (ys 0) head rest ![bit,head,rest]
    (hq 0) (projectionValue 1 ![bit,head,rest]) (projectionValue 2 ![bit,head,rest])
  have hp := binaryRecover InternalPairing.pairing (.projection 0) kept (ys 1) bit (ys 0) ![bit,head,rest]
    (hq 1) (projectionValue 0 ![bit,head,rest]) (hq 0)
  have hw := unaryRecover (Fold.weighted weight) kept (ys 2) (ys 0) ![bit,head,rest] (hq 2) (hq 0)
  exact ⟨hk,hp,hw⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseConstructQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseConstructQueriesProof
