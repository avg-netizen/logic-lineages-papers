module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxChildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralCoveredTypedAuxChildProof (exact_OpenCoveredTypedFunctionChild)
open NumberedWindowInternalLiteralAuxOwnFuelCasesProof (exact_OpenTypedAuxiliaryOwnFuelCases)

def ActiveRaw (C : Program 3) (s : Settings) (leaf : Nat → Program 3) (other : Program 3) (base : Program 2)
    (T V : Program 1) : Program 5 :=
  typedRaw5 (root (leafAtAuxiliary leaf)) (auxiliaryFallback (fallback other)) (coveredMemoWindow C s base T V) V

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem endpointGuardsRename {β : Type} (W : Program 3) (V : Program 1)
    (ctx ty q r : OTerm α) (j : α → β) :
    (liftedEndpointGuards W V ctx ty q r).relabel j =
      liftedEndpointGuards W V (ctx.relabel j) (ty.relabel j) (q.relabel j) (r.relabel j) := by
  simp only [liftedEndpointGuards,conjunctionRename,programRename,tripleInputsRename,sucRelabel,zRelabel]
  congr <;> funext i <;> obtain rfl := Fin.eq_zero i <;> rfl

/-- The inherited function step has the exact same physically selected
raw checker as the parent, with its same-context typing guards and its
own accepting witness. The unchanged argument is a genuine typed
window report. Their own selected least programs are shown to succeed;
no quotient transport between different raw representatives is assumed. -/
theorem exact_OpenCoveredTypedAuxChildCases (C : Program 3) (X : Program 2) (s : Settings) (leaf : Nat → Program 3) (other : Program 3) (base : Program 2)
    (T V : Program 1) (ctx ty q w r : OTerm α) (goal : Formula α)
    (aux : D B Γ (bit sourceIsAux ![q,w,r]))
    (held : D B Γ (programGraph (typedRaw5 (root (leafAtAuxiliary leaf))
      (auxiliaryFallback (fallback other)) (coveredMemoWindow C s base T V) V) (suc z) ![ctx,ty,q,w,r]))
    (beta : D B Γ (liftedEndpointGuards (coveredMemoWindow C s base T V) V ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
        D B Δ (bit (leaf 6) ![q.relabel j,payload,r.relabel j]) →
        D B Δ (bit functionLambdaHeader ![q.relabel j,payload,r.relabel j]) →
        D B Δ (goal.relabel j))
    (bottom : D B Γ (liftedEndpointGuards (coveredMemoWindow C s base T V) V ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
        D B Δ (bit (leaf 7) ![q.relabel j,payload,r.relabel j]) →
        D B Δ (bit targetBottom ![q.relabel j,payload,r.relabel j]) →
        D B Δ (goal.relabel j))
    (context : D B Γ (liftedEndpointGuards (coveredMemoWindow C s base T V) V ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (dom cod fn arg child dom' cod' dest arg' : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
          dom cod fn arg child dom' cod' dest arg' →
        D B Δ (programGraph (ActiveRaw C s leaf other base T V) (suc z)
          ![ctx.relabel j,rawCons dom cod,fn,child,dest] ⊓
          (childAtWindow (coveredMemoWindow C s base T V) V (ctx.relabel j) dom arg ⊓
            (hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) (rawCons dom cod) fn ⊓
              (hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) (rawCons dom cod) dest ⊓
                hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) dom arg)))) →
        D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenTypedAuxiliaryOwnFuelCases leaf other (coveredMemoWindow C s base T V) V ctx ty q w r goal aux held
  · exact beta
  · exact bottom
  · intro guards β j Δ dom cod fn arg child dom' cod' dest arg' keep fields success
    have same := renameInto guards j Δ keep
    rw [endpointGuardsRename] at same
    have typedChild := exact_OpenCoveredTypedFunctionChild C X s (root (leafAtAuxiliary leaf))
      (auxiliaryFallback (fallback other)) base T V (ctx.relabel j) (ty.relabel j)
      (q.relabel j) (w.relabel j) (r.relabel j) dom cod fn arg child dom' cod' dest arg'
      fields same success
    exact context guards β j Δ dom cod fn arg child dom' cod' dest arg' keep fields typedChild

#print axioms exact_OpenCoveredTypedAuxChildCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxCasesProof
