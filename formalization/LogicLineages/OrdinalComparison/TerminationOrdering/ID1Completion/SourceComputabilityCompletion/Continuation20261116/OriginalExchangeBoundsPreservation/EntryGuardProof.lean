module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalApplicationStepPeelSupportProof (andIntro)
open Continuation20261115

theorem children (n : Nat) (raw typ head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (suc z) head ⊓
       graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases EntryGuardQueriesProof.queries ![head,tail] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![head,tail] i).relabel j) = ![head.relabel j,tail.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  simp only [conjunctionRename,graph1Rename,sucRelabel,zRelabel]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  rw [graph3Rename] at hcj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  obtain ⟨hr,hl⟩ := EntryGuardQueriesProof.recover (head.relabel j) (tail.relabel j) ys hq
  obtain ⟨hh,ht⟩ := EntryGuardChildrenProof.atLists n (raw.relabel j) (typ.relabel j)
    (head.relabel j) (tail.relabel j) (ys 0) (ys 1) hcj hgj hr hl
  exact andIntro hh ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardProof
