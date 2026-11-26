module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseSearchCompletenessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountHeadQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z eqn)
open Continuation20261114
def head : Program 1 := InternalListCodec.headCode
def tail : Program 1 := InternalListCodec.tailCode
def count : Program 1 := .composition ArgumentEntryCount.count ![tail,head]
def queries : Fin 3 → Program 1 := ![head,tail,count]

theorem recover (raw : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![raw]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count (ys 2) (ys 1) (ys 0))) := by
  exact ⟨InternalListCodecDecompositionSupportProof.reconstructNonzero raw (ys 0) (ys 1) hn (hq 0) (hq 1),
    binaryRecover ArgumentEntryCount.count tail head (ys 2) (ys 1) (ys 0) ![raw] (hq 2) (hq 1) (hq 0)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountHeadQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountHeadQueriesProof
