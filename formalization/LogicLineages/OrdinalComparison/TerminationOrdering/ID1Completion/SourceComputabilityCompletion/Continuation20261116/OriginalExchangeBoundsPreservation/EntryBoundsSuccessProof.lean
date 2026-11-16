module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsStepQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsSuccessProof
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
open Continuation20261114 Continuation20261115

theorem success (n : Nat) (raw typ head tail param entries value tailEntries : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hf : Nonempty (Derivation body Delta (graph1 (Fold.weighted (Fold.entryWeight n)) value entries)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) value raw)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (EntryBoundsStepQueriesProof.queries n) ![typ,head,tailEntries] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![typ,head,tailEntries] i).relabel j) = ![typ.relabel j,head.relabel j,tailEntries.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [graph1Rename]
  obtain ⟨hp,hl,htf,hh⟩ := EntryBoundsStepQueriesProof.recover n (typ.relabel j) (head.relabel j) (tailEntries.relabel j) ys hq
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hej := renameInto he j Theta hj
  have hfj := renameInto hf j Theta hj
  have htj := renameInto ht j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph3Rename] at hcj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj hfj
  simp only [graph2Rename,sucRelabel] at hej htj
  rw [belowRawRename] at ihj
  exact EntryBoundsStepAtProof.atValues n (raw.relabel j) (typ.relabel j) (head.relabel j) (tail.relabel j)
    (param.relabel j) (entries.relabel j) (value.relabel j) (tailEntries.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    hcj hgj hej hfj htj hp hl htf hh ihj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsSuccessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsSuccessProof
