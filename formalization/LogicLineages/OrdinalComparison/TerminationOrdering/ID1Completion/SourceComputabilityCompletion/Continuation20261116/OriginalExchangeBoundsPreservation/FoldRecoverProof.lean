module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldRecoverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalTagArithmeticSyntaxProof (eqn)

theorem cons (weight : Program 1) (list head tail tailSum w out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hw : Nonempty (Derivation body Delta (graph1 weight w head)))
    (ho : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) out list))) :
    Nonempty (Derivation body Delta (graph2 merge out w tailSum)) := by
  apply programCases merge ![w,tailSum] _
  intro beta j Theta merged hj hm
  have hx : (fun i => (![w,tailSum] i).relabel j) = ![w.relabel j,tailSum.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hm
  rw [graph2Rename]
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hwj := renameInto hw j Theta hj
  have hoj := renameInto ho j Theta hj
  rw [graph2Rename] at hcj
  rw [graph1Rename] at htj hwj hoj
  have hv := FoldValueProof.cons weight (list.relabel j) (head.relabel j) (tail.relabel j)
    (tailSum.relabel j) (w.relabel j) merged hcj htj hwj hm
  have he := valueUnique (Fold.weighted weight) merged (out.relabel j) ![list.relabel j] hv hoj
  exact outputTransport merge merged (out.relabel j) ![w.relabel j,tailSum.relabel j] he hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldRecoverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldRecoverProof
