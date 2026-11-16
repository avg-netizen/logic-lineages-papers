module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTypedDecoderInternalAcceptance
open Continuation20261115 Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atConstructor (n : Nat) (H : Program 1)
    (raw head child typ gamma pair size label depth : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hgc : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)))
    (ht : Nonempty (Derivation body Delta (TermAccepted H typ raw gamma)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw))) :
    Nonempty (Derivation body Delta (result false size depth)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (OrdinaryQueryProof.queries H) ![head,child] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![head,child] i).relabel j) =
      ![head.relabel j,child.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hpayload,hsignature,hfields⟩ := OrdinaryQueryProof.recover H
    (head.relabel j) (child.relabel j) ys hq
  rw [SyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hgcj := renameInto hgc j Theta hj
  have htj := renameInto ht j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at hcj hgj hgcj hbj hpj hdj
  rw [OriginalTypedDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] at htj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hpair := PayloadProof.ordinary (raw.relabel j) (head.relabel j) (child.relabel j) (ys 0) hcj hpayload
  have hchild := ModeChildrenProof.ordinaryChildren H (raw.relabel j) (ys 0) (head.relabel j)
    (child.relabel j) (ys 1) (ys 2) (ys 3) (typ.relabel j) (gamma.relabel j) hpair hpayload hsignature hfields htj
  exact UnaryInductionProof.step true n H (raw.relabel j) (head.relabel j) (child.relabel j)
    (pair.relabel j) (size.relabel j) (label.relabel j) (depth.relabel j) (ys 3) (gamma.relabel j)
    hcj hgj hbj hpj hdj ihj (DescentProof.ordinary _ _ _ hcj) hgcj hchild

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryBranchProof
