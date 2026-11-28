module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundAboveBetaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardRecoveryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundOrderAcceptedProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof (exact_OpenSingletonBoundBeforeDepth)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenBetaLambdaBodyTargetAt)
open NumberedWindowInternalLiteralSingletonGuardRecoveryProof
  (exact_OpenAcceptedBetaSingletonLambdaChildGuards)
open NumberedWindowInternalLiteralSingletonLambdaBoundAboveBetaProof
  (exact_OpenBetaLambdaBoundAboveTarget)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A bound index below the depth under one lambda keeps the original
node. The accepted beta graph supplies the syntax guards. -/
theorem exact_OpenAcceptedBetaLambdaBoundBefore (V : Program 1) (H : Program 2) (W : Program 3)
    (a body ty t i r : OTerm α)
    (shape : D B Γ (eqn body (rawLambdaTerm ty (boundTerm t i))))
    (before : D B Γ (ltF i (suc z)))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc r) ![a,body])) :
    D B Γ (eqn (suc r) (suc (rawLambdaTerm ty (boundTerm t i)))) := by
  obtain ⟨inserted,lambdaNode,boundNode⟩ :=
    exact_OpenAcceptedBetaSingletonLambdaChildGuards V H W a body ty (boundTerm t i) r shape held
  have child := exact_OpenSingletonBoundBeforeDepth V H W a (suc z) t i
    inserted boundNode before
  exact exact_OpenBetaLambdaBodyTargetAt V H (singletonBound V H W)
    a body ty (boundTerm t i) (boundTerm t i) r inserted lambdaNode shape child held

/-- A bound index above the depth under one lambda is decremented. The
continuation obtains the predecessor of the original index and the rebuilt
target. The accepted beta graph supplies the syntax guards. -/
theorem exact_OpenAcceptedBetaLambdaBoundAbove (V : Program 1) (H : Program 2) (W : Program 3)
    (a body ty t i r : OTerm α) (goal : Formula α)
    (shape : D B Γ (eqn body (rawLambdaTerm ty (boundTerm t i))))
    (above : D B Γ (ltF (suc z) i))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc r) ![a,body]))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (eqn (i.relabel ρ) (suc j)) →
      D B Δ (eqn (suc (r.relabel ρ))
        (suc (rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) j)))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal := by
  obtain ⟨inserted,lambdaNode,boundNode⟩ :=
    exact_OpenAcceptedBetaSingletonLambdaChildGuards V H W a body ty (boundTerm t i) r shape held
  exact exact_OpenBetaLambdaBoundAboveTarget V H W a body ty t i r goal
    inserted lambdaNode boundNode shape above held use

#print axioms exact_OpenAcceptedBetaLambdaBoundBefore
#print axioms exact_OpenAcceptedBetaLambdaBoundAbove
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundOrderAcceptedProof
