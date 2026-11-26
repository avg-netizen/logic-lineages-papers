module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.RawStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.MalformedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.EndpointSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro andLeft)
open Continuation20261115 Induction

theorem internalTerm : Targets.InternalTermDepthBound := by
  intro n H body alpha Delta typ raw gamma pair size label depth ht hb hp hd
  apply OriginalCodeBoundsRecursion.CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    rw [EndpointSyntaxProof.termRename]
    have hdj := renameInto hd j Theta hj
    rw [graph1Rename] at hdj
    exact MalformedProof.termBound n (raw.relabel j) (depth.relabel j) (size.relabel j) hg hdj
  · intro beta j Theta hj hg
    rw [EndpointSyntaxProof.termRename]
    have htj := renameInto ht j Theta hj
    have hbj := renameInto hb j Theta hj
    have hpj := renameInto hp j Theta hj
    have hdj := renameInto hd j Theta hj
    rw [OriginalTypedDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] at htj
    rw [graph1Rename] at hbj hdj
    rw [graph2Rename] at hpj
    have ho : Nonempty (Derivation body Theta
        (observations n H false (raw.relabel j)
          ![typ.relabel j,gamma.relabel j,pair.relabel j,size.relabel j,label.relabel j,depth.relabel j])) :=
      andIntro (andIntro (andIntro (andIntro hg htj) hbj) hpj) hdj
    have hi : Nonempty (Derivation body Theta (AtRaw n H (raw.relabel j))) := RawStepProof.allRaw n H (raw.relabel j)
    have hresult := InductionBindingProof.atRawApply n H false (raw.relabel j)
      ![typ.relabel j,gamma.relabel j,pair.relabel j,size.relabel j,label.relabel j,depth.relabel j] hi ho
    exact andLeft hresult

theorem internalArguments : Targets.InternalArgumentsDepthBound := by
  intro n H body alpha Delta typ raw gamma pair size label depth ht hb hp hd
  apply OriginalCodeBoundsRecursion.CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    rw [EndpointSyntaxProof.argumentsRename]
    have hdj := renameInto hd j Theta hj
    rw [graph1Rename] at hdj
    exact MalformedProof.argumentsBound n (raw.relabel j) (depth.relabel j) (size.relabel j) hg hdj
  · intro beta j Theta hj hg
    rw [EndpointSyntaxProof.argumentsRename]
    have htj := renameInto ht j Theta hj
    have hbj := renameInto hb j Theta hj
    have hpj := renameInto hp j Theta hj
    have hdj := renameInto hd j Theta hj
    rw [OriginalTypedDecoderInternalAcceptanceSyntaxProof.argumentsAcceptedRename] at htj
    rw [graph1Rename] at hbj hdj
    rw [graph2Rename] at hpj
    have ho : Nonempty (Derivation body Theta
        (observations n H true (raw.relabel j)
          ![typ.relabel j,gamma.relabel j,pair.relabel j,size.relabel j,label.relabel j,depth.relabel j])) :=
      andIntro (andIntro (andIntro (andIntro hg htj) hbj) hpj) hdj
    have hi : Nonempty (Derivation body Theta (AtRaw n H (raw.relabel j))) := RawStepProof.allRaw n H (raw.relabel j)
    have hresult := InductionBindingProof.atRawApply n H true (raw.relabel j)
      ![typ.relabel j,gamma.relabel j,pair.relabel j,size.relabel j,label.relabel j,depth.relabel j] hi ho
    exact hresult
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Proof
