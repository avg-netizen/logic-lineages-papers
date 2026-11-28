module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityTypingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityConsumerProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenPhysicalBetaBoundZero)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)
open NumberedWindowInternalLiteralSingletonGuardRecoveryProof (exact_OpenAcceptedBetaSingletonSyntax)
open NumberedWindowInternalLiteralBetaIdentityProof (exact_OpenAlignedIdentityBetaComputability)
open NumberedWindowInternalLiteralBetaIdentityTypingProof (exact_OpenIdentityBetaTypeFromHop)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual hop supplies the identity row's type alignment. The accepted
singleton run supplies its replacement output, so the original argument's
computability reaches the emitted address without a separate type equation. -/
theorem exact_OpenAlignedIdentityBetaFromHop
    (s : Settings) (base H : Program 2) (T V TV baseM i cv tv : Program 1)
    (leaf : Nat → Program 3) (other L₀ U p : Program 3) (τ : Ty)
    {x u ctx result dom cod fn arg sc st before cert after q w r d e f a bind body y bodyType : OTerm α}
    (parsed : D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg))
    (row : AlignedBetaRow L₀ (guardedLeast (headerLeast (fullAuxiliaryDecorator L₀)))
      (zeroDepthInstance (singletonLambda (unitAuxSyntax V TV) H U))
      B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (checked : D B Γ (hopCalls
      (rawWithTarget i cv tv (selectedJoinedRaw s base T V TV baseM leaf other)
        (guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))))
      (guardedLeast (headerLeast (fullAuxiliaryDecorator L₀)))
      sc st before cert after q w r))
    (scope : D B Γ (eqn sc ctx))
    (identity : D B Γ (eqn body (boundTerm bodyType z)))
    (argument : D B Γ (formula p τ u)) : D B Γ (formula p τ y) := by
  let Va := unitAuxSyntax V TV
  let I := zeroDepthInstance (singletonLambda Va H U)
  let node := boundTerm bodyType z
  have held := exact_OpenInstanceBodyTransport I (suc r) a body node identity row.instanceRun
  obtain ⟨inserted,typedNode⟩ := exact_OpenAcceptedBetaSingletonSyntax Va H U a node r held
  have run : D B Γ (programGraph I (suc a) ![a,node]) :=
    exact_OpenPhysicalBetaBoundZero Va H (singletonLambdaDispatch U) a bodyType inserted typedNode
  obtain ⟨output⟩ := valueUnique I (suc r) (suc a) ![a,node] held run
  have sameType := exact_OpenIdentityBetaTypeFromHop s base T V TV baseM i cv tv leaf other
    (guardedLeast (headerLeast (fullAuxiliaryDecorator L₀)))
    sc st before cert after q w r d e f a checked row.source ⟨cancelSuc output⟩
  exact exact_OpenAlignedIdentityBetaComputability L₀ Va H U p τ parsed row scope sameType identity argument

#print axioms exact_OpenAlignedIdentityBetaFromHop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityConsumerProof
