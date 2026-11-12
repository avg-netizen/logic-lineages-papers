module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem lambdaRaw (source : Program 2) (oldStep : Program 4) :
 OriginalGenericLambdaWrapperTargets.RawIntroduction source (OriginalTransparentMixedPathDefinitions.refined source oldStep) := by
 intro body alpha Delta s t cert parameter childS childT childCert childParam d e context gamma extended hh hchild
 have hi := OriginalTransparentMixedPathLambdaPrefixProof.hop source oldStep
  s t cert parameter childS childT childCert childParam d e context gamma extended InternalOriginalStepGuard.one hh
 obtain ⟨hb⟩ := andRight hi
 obtain ⟨hc⟩ := hchild
 exact ⟨Derivation.implicationElimination hb hc⟩

theorem applicationRaw (source : Program 2) (oldStep : Program 4) :
 OriginalGenericApplicationWrapperTargets.RawIntroduction source (OriginalTransparentMixedPathDefinitions.refined source oldStep) := by
 intro body alpha Delta s t cert parameter childS childT childCert arg d e arrow hh hchild
 have hi := OriginalTransparentMixedPathApplicationPrefixProof.hop source oldStep
  s t cert parameter childS childT childCert arg d e arrow InternalOriginalStepGuard.one hh
 obtain ⟨hb⟩ := andRight hi
 obtain ⟨hc⟩ := hchild
 exact ⟨Derivation.implicationElimination hb hc⟩

theorem actualLambda : OriginalMixedClosedPrefixTargets.ActualLambda := by
 intro source oldStep endpoint window
 exact OriginalGenericLambdaWrapperProof.actualOriginalTransparentLambdaClosedLeafIntroduction
  source (OriginalTransparentMixedPathDefinitions.refined source oldStep) endpoint window (lambdaRaw source oldStep)

theorem actualApplication : OriginalMixedClosedPrefixTargets.ActualApplication := by
 intro source oldStep endpoint window
 exact OriginalGenericApplicationWrapperProof.actualIntroduction
  source (OriginalTransparentMixedPathDefinitions.refined source oldStep) endpoint window (applicationRaw source oldStep)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrefixProof
