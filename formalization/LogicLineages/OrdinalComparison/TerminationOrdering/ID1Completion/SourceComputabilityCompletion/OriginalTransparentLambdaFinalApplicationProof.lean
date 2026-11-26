module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationCombineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldLaws
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityClosure
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open OriginalTransparentLambdaFinalApplicationSelectorProof
open OriginalTransparentLambdaFinalApplicationNodeProof
open OriginalTransparentLambdaFinalApplicationAcceptanceProof
open OriginalTransparentLambdaFinalApplicationCombineProof
open OriginalTransparentLambdaFinalFoldLaws
open InternalParameterizedApplicationValidityFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual SAME-member source callback compatibility at every original
application and every pair of actual child outputs, including rejection. -/
theorem sourceApplicationLaw (body : Positive (Fin 1))
    (data : InternalOriginalUniformDescentSelection.Data) :
    ApplicationLaw body openingGuardP (sourceValidator data)
      (combineP (normalizedData data).member) := by
  intro alpha Gamma arrow d e fp ap fn arg parent fo ao out parameter hc _ hf ha ho
  let N := normalizedData data
  have hs := rawTypeAndTag arrow d e fp ap fn arg parent hc
  have hn := sourceApplicationNode N parent parameter e (andLeft hs) (andRight hs)
  have hchildren := childrenEquation (sourceRoot N) (targetRoot N) N.member
    arrow d e fp ap fn arg parent parameter hc
  have he := acceptanceAtChildren (sourceRoot N) (targetRoot N) N.member N.member
    parent parameter e fn arg (andRight hs) hn hchildren
  exact combineTransport N.member (sourceRoot N) (targetRoot N) N.member
    d e fo ao fn arg parent out parameter hf ha he ho

/-- The target uses constant one for both node callbacks and membership.
No source-window premise is introduced. -/
theorem targetApplicationLaw (body : Positive (Fin 1))
    (data : InternalOriginalUniformDescentSelection.Data) :
    ApplicationLaw body openingGuardP (targetValidator data)
      (combineP (InternalLessThan.constantOne 2)) := by
  intro alpha Gamma arrow d e fp ap fn arg parent fo ao out parameter hc _ hf ha ho
  let N := normalizedData data
  let one := InternalLessThan.constantOne 2
  have hs := rawTypeAndTag arrow d e fp ap fn arg parent hc
  have hn := targetApplicationNode N parent parameter e (andLeft hs) (andRight hs)
  have hchildren := childrenEquation (targetRoot N) one one
    arrow d e fp ap fn arg parent parameter hc
  have he := acceptanceAtChildren (targetRoot N) one one one
    parent parameter e fn arg (andRight hs) hn hchildren
  exact combineTransport one (targetRoot N) one one
    d e fo ao fn arg parent out parameter hf ha he ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationProof
