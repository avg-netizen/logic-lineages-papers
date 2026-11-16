module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open Continuation20261115 Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem step (n : Nat) (H : Program 1)
    (raw rootLabel head typ left types right pair size label depth leftTyp rightTyp gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw)))
    (hls : Nonempty (Derivation body Delta (InternalLessThan.strictLess left raw)))
    (hrs : Nonempty (Derivation body Delta (InternalLessThan.strictLess right raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlt : Nonempty (Derivation body Delta (accepted H true leftTyp left gamma)))
    (hrt : Nonempty (Derivation body Delta (accepted H true rightTyp right gamma)))
    : Nonempty (Derivation body Delta (result false size depth)) := by
  apply OriginalEnumerationDepth.BinaryQueriesProof.cases n left right (result false size depth)
  intro beta j Theta dl dr maximum hj hld hrd hm
  rw [SyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have ihj := renameInto ih j Theta hj
  have hlsj := renameInto hls j Theta hj
  have hrsj := renameInto hrs j Theta hj
  have hlgj := renameInto hlg j Theta hj
  have hrgj := renameInto hrg j Theta hj
  have hltj := renameInto hlt j Theta hj
  have hrtj := renameInto hrt j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at hgj hbj hpj hdj hlgj hrgj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hlsj hrsj
  rw [SyntaxProof.acceptedRename] at hltj hrtj
  exact NumberedInductionProof.atDepth n H (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j)
    (pair.relabel j) (size.relabel j) (label.relabel j) (depth.relabel j)
    (leftTyp.relabel j) (rightTyp.relabel j) (gamma.relabel j) dl dr maximum
    hcj hgj hbj hpj hdj ihj hlsj hrsj hlgj hrgj hltj hrtj hld hrd hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedClosureProof
