module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryGuardChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryGuardProof
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

theorem child (ordinary : Bool) (n : Nat) (raw metadata child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (if ordinary then OriginalRawSyntaxTransport.ordinaryConstructor else OriginalRawSyntaxTransport.lambdaConstructor) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases EntryGuardQueriesProof.queries ![child,child] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![child,child] i).relabel j) = ![child.relabel j,child.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  simp only [graph1Rename,sucRelabel,zRelabel]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  rw [graph2Rename] at hcj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  obtain ⟨hr,_hl⟩ := EntryGuardQueriesProof.recover (child.relabel j) (child.relabel j) ys hq
  exact UnaryGuardChildrenProof.atList ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j) (ys 0) hcj hgj hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryGuardProof
