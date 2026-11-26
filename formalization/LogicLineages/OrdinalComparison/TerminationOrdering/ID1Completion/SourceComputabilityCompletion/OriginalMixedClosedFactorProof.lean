module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedFactorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedFactorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryLambdaGlobal OriginalHereditaryLambda
open OriginalHereditaryLambdaGlobalInternalProof (wrapperFactor)
open InternalAcceptanceConjunctionProof
open OriginalLambdaGuardLeafInternalProof (projectLeft)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Both wrapper layers and the hereditary conjunction are stripped at the
same root inputs, using only original arithmetic graph elimination. -/
theorem factor (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (accepted (closedLeaf endpoint window oldStep) s t cert parameter))) :
 Nonempty (Derivation body Delta (accepted oldStep s t cert parameter)) := by
 let inner := wrapper endpoint window oldStep
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have hh := wrapperFactor endpoint window (refined inner) s t cert parameter h
 have hi := projectLeft (conjunctionRecover inner (guard inner) xs hh)
 exact wrapperFactor endpoint window oldStep s t cert parameter hi
theorem actualRawFactor : OriginalMixedClosedFactorTargets.ActualRawFactor := by
 intro H G M W oldStep window body alpha Delta s t cert parameter h
 exact factor (OriginalMixedLiteralEndpointDefinitions.endpoint H G M W) window
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) body alpha Delta s t cert parameter h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedFactorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedFactorProof
