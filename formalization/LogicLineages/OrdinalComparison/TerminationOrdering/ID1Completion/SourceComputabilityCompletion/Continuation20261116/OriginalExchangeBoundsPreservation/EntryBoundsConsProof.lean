module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.MergeComponentsQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsProof
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
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open Continuation20261115

theorem cons (n : Nat) (raw typ head tail hv tv out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hh : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) hv head)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) tv tail)))
    (hm : Nonempty (Derivation body Delta (graph2 merge out hv tv))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) out raw)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases MergeComponentsQueriesProof.queries ![hv,tv] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![hv,tv] i).relabel j) = ![hv.relabel j,tv.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [graph1Rename]
  obtain ⟨hlp,hrp,hmax⟩ := MergeComponentsQueriesProof.recover (hv.relabel j) (tv.relabel j) ys hq
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hhj := renameInto hh j Theta hj
  have htj := renameInto ht j Theta hj
  have hmj := renameInto hm j Theta hj
  rw [graph3Rename] at hcj
  rw [graph1Rename] at hhj htj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  rw [graph2Rename] at hmj
  exact EntryBoundsConsAtProof.cons n (raw.relabel j) (typ.relabel j) (head.relabel j) (tail.relabel j)
    (hv.relabel j) (ys 0) (ys 1) (tv.relabel j) (ys 2) (ys 3) (ys 4) (out.relabel j)
    hcj hgj hhj htj hlp hrp hmax hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsProof
