module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ApplicationBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTypedDecoderInternalAcceptance
open Continuation20261115 Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atConstructor (n : Nat) (H : Program 1)
    (raw domain left right typ gamma pair size label depth : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (ht : Nonempty (Derivation body Delta (TermAccepted H typ raw gamma)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw))) :
    Nonempty (Derivation body Delta (result false size depth)) := by
  apply InternalAcceptanceSupportProof.programCases InternalListCodec.consCode ![domain,typ] _
  intro beta j Theta arrow hj harrow
  have hx : (fun i => (![domain,typ] i).relabel j) = ![domain.relabel j,typ.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at harrow
  rw [SyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hlgj := renameInto hlg j Theta hj
  have hrgj := renameInto hrg j Theta hj
  have htj := renameInto ht j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel] at hcj hgj hlgj hrgj hbj hpj hdj
  rw [OriginalTypedDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] at htj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  obtain ⟨hi⟩ := OriginalTypedDecoderTransportBinaryAcceptanceProof.applicationIff H
    (raw.relabel j) (domain.relabel j) (left.relabel j) (right.relabel j)
    (typ.relabel j) arrow (gamma.relabel j) hcj harrow
  have hchildren := Derivation.implicationElimination (Derivation.conjunctionLeft hi) (Classical.choice htj)
  have hs := DescentProof.application _ _ _ _ hcj
  exact BinaryClosureProof.step false n H (raw.relabel j) (domain.relabel j) (left.relabel j) (right.relabel j)
    (pair.relabel j) (size.relabel j) (label.relabel j) (depth.relabel j) arrow (domain.relabel j) (gamma.relabel j)
    hcj hgj hbj hpj hdj ihj (andLeft hs) (andRight hs) hlgj hrgj
    ⟨Derivation.conjunctionLeft hchildren⟩ ⟨Derivation.conjunctionRight hchildren⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ApplicationBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ApplicationBranchProof
