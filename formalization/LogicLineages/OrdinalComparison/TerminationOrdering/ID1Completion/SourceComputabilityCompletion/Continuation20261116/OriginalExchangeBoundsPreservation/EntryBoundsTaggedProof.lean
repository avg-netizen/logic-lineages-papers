module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsCaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsTaggedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EntryBounds EntryBoundsSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115

theorem consTag (n : Nat) (raw param entries value : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 7) raw)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hf : Nonempty (Derivation body Delta (graph1 (Fold.weighted (Fold.entryWeight n)) value entries)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) value raw)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ htag
  intro beta j Theta typ head tail hj hc
  rw [graph1Rename]
  have hgj := renameInto hg j Theta hj
  have hej := renameInto he j Theta hj
  have hfj := renameInto hf j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj hfj
  simp only [graph2Rename,sucRelabel] at hej
  rw [belowRawRename] at ihj
  exact EntryBoundsConsCaseProof.cons n (raw.relabel j) typ head tail (param.relabel j)
    (entries.relabel j) (value.relabel j) hc hgj hej hfj ihj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsTaggedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsTaggedProof
