module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxThreeWaysProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelBridgeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralAuxThreeWaysProof (exact_OpenTypedAuxiliaryThreeWays)
open NumberedWindowInternalLiteralAuxOwnFuelBridgeProof (exact_OpenFunctionChildOwnFuel)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The scoped auxiliary raw-step split now yields the actual child's
own-code accepting graph (not the parent's fuel) in the function
case. The two root cases retain the original selected leaf calls. -/
theorem exact_OpenTypedAuxiliaryOwnFuelCases (leaf : Nat → Program 3) (other window : Program 3)
    (syntaxCheck : Program 1) (ctx ty q w r : OTerm α) (goal : Formula α)
    (aux : D B Γ (bit sourceIsAux ![q,w,r]))
    (held : D B Γ (programGraph (typedRaw5 (root (leafAtAuxiliary leaf))
      (auxiliaryFallback (fallback other)) window syntaxCheck) (suc z) ![ctx,ty,q,w,r]))
    (beta : D B Γ (liftedEndpointGuards window syntaxCheck ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
        D B Δ (bit (leaf 6) ![q.relabel j,payload,r.relabel j]) →
        D B Δ (bit functionLambdaHeader ![q.relabel j,payload,r.relabel j]) →
        D B Δ (goal.relabel j))
    (bottom : D B Γ (liftedEndpointGuards window syntaxCheck ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
        D B Δ (bit (leaf 7) ![q.relabel j,payload,r.relabel j]) →
        D B Δ (bit targetBottom ![q.relabel j,payload,r.relabel j]) →
        D B Δ (goal.relabel j))
    (context : D B Γ (liftedEndpointGuards window syntaxCheck ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (dom cod fn arg child dom' cod' dest arg' : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
          dom cod fn arg child dom' cod' dest arg' →
        D B Δ (bit (ownRun (root (leafAtAuxiliary leaf)) (auxiliaryFallback (fallback other))) ![fn,child,dest]) →
        D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenTypedAuxiliaryThreeWays leaf (fallback other) window syntaxCheck ctx ty q w r goal aux held
  · exact beta
  · exact bottom
  · intro guards β j Δ dom cod fn arg child dom' cod' dest arg' keep fields success
    exact context guards β j Δ dom cod fn arg child dom' cod' dest arg' keep fields
      (exact_OpenFunctionChildOwnFuel (root (leafAtAuxiliary leaf)) other fn child dest success)

#print axioms exact_OpenTypedAuxiliaryOwnFuelCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelCasesProof
