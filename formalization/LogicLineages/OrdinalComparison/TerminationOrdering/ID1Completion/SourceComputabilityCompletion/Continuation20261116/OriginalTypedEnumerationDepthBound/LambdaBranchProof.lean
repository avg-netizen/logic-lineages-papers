module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaBranchProof
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
    (raw domain child typ gamma pair size label depth : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hgc : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)))
    (ht : Nonempty (Derivation body Delta (TermAccepted H typ raw gamma)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw))) :
    Nonempty (Derivation body Delta (result false size depth)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases LambdaQueryProof.queries ![domain,child,typ,gamma] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![domain,child,typ,gamma] i).relabel j) =
      ![domain.relabel j,child.relabel j,typ.relabel j,gamma.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hpayload,hext,hfields⟩ := LambdaQueryProof.recover
    (domain.relabel j) (child.relabel j) (typ.relabel j) (gamma.relabel j) ys hq
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
  have hpair := PayloadProof.lambdaCode (raw.relabel j) (domain.relabel j) (child.relabel j) (ys 0) hcj hpayload
  have hchild := ModeChildrenProof.lambdaChildren H (raw.relabel j) (ys 0) (domain.relabel j)
    (child.relabel j) (typ.relabel j) (ys 2) (ys 3) (gamma.relabel j) (ys 1) hpair hpayload hfields hext htj
  exact UnaryInductionProof.step false n H (raw.relabel j) (domain.relabel j) (child.relabel j)
    (pair.relabel j) (size.relabel j) (label.relabel j) (depth.relabel j) (ys 3) (ys 1)
    hcj hgj hbj hpj hdj ihj (DescentProof.lambdaCode _ _ _ hcj) hgcj hchild
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaBranchProof
