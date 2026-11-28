module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundHitBetaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardRecoveryProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundHitAcceptedProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonGuardRecoveryProof
  (exact_OpenAcceptedBetaSingletonLambdaChildGuards)
open NumberedWindowInternalLiteralSingletonLambdaBoundHitBetaProof
  (exact_OpenBetaLambdaBoundHitTarget)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- At the discharged index under one binder, the accepted instance
itself supplies all three guards needed by the beta consumer. -/
theorem exact_OpenAcceptedBetaLambdaBoundHit (V : Program 1) (H : Program 2) (W : Program 3)
    (a body lamTy t r : OTerm α) (goal : Formula α)
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc r) ![a,body]))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (programGraph H (suc u) ![a.relabel ρ,suc z]) →
      D B Δ (eqn (suc (r.relabel ρ)) (suc (rawLambdaTerm (lamTy.relabel ρ) u))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal := by
  obtain ⟨inserted,lambdaNode,boundNode⟩ :=
    exact_OpenAcceptedBetaSingletonLambdaChildGuards V H W a body lamTy (boundTerm t (suc z)) r
      shape held
  exact exact_OpenBetaLambdaBoundHitTarget V H W a body lamTy t r goal
    inserted lambdaNode boundNode shape held use

/-- The aligned row contributes its own accepted instance. The caller's
body case supplies the literal lambda and discharged-index equation. -/
theorem exact_OpenAcceptedAlignedBetaLambdaBoundHit (L₀ L : Program 3)
    (V : Program 1) (H : Program 2) (W : Program 3)
    (ctx dom cod fn arg sc st after q r d e f a bind body y lamTy t : OTerm α)
    (goal : Formula α)
    (row : AlignedBetaRow L₀ L (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (programGraph H (suc u) ![a.relabel ρ,suc z]) →
      D B Δ (eqn (suc (r.relabel ρ)) (suc (rawLambdaTerm (lamTy.relabel ρ) u))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal :=
  exact_OpenAcceptedBetaLambdaBoundHit V H W a body lamTy t r goal shape row.instanceRun use

#print axioms exact_OpenAcceptedBetaLambdaBoundHit
#print axioms exact_OpenAcceptedAlignedBetaLambdaBoundHit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundHitAcceptedProof
