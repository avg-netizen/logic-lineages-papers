module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxTypedInversionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxThreeWaysProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux auxiliaryFallback)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalLiteralAuxRootLeafOpenProof (exact_OpenAuxiliaryRootLeafCases)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRunChildProof (ChildTerminal)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralAuxTypedInversionProof (exact_OpenTypedAuxiliaryInversion)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveAuxInputs (q w r w' r' : OTerm α) (held : D B Γ (bit sourceIsAux ![q,w,r])) :
    D B Γ (bit sourceIsAux ![q,w',r']) := by
  have k : D B Γ (unary termShape (suc z) q) := by
    apply compositionRecover termShape (fun _ : Fin 1 => .projection 0) (suc z) ![q,w,r] ![q] held
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 ![q,w,r]
  exact onTape termShape 0 (suc z) ![q,w',r'] k

/-- Exactly three raw cases for an accepted typed hop from the selected
auxiliary source. The root branches report the physical beta and bottom
observations; the contextual branch exposes the exact function fields,
same raw argument, and the original remaining-fuel child loop. The four
original outer window/syntax observations are carried independently. -/
theorem exact_OpenTypedAuxiliaryThreeWays (leaf : Nat → Program 3) (other window : Program 3)
    (syntaxCheck : Program 1) (ctx ty q w r : OTerm α) (goal : Formula α)
    (aux : D B Γ (bit sourceIsAux ![q,w,r]))
    (held : D B Γ (programGraph (typedRaw5 (root (leafAtAuxiliary leaf))
      (auxiliaryFallback other) window syntaxCheck) (suc z) ![ctx,ty,q,w,r]))
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
        D B Δ (ChildTerminal (root (leafAtAuxiliary leaf)) other fn child dest) →
        D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenTypedAuxiliaryInversion (leafAtAuxiliary leaf) other window syntaxCheck ctx ty q w r goal aux held
  · intro guards tag arity known β j Δ payload keep witness _ accepted
    let xs : Fin 3 → OTerm β := ![q.relabel j,payload,r.relabel j]
    have lifted := moveBit sourceIsAux q w r j Δ keep aux
    have same := moveAuxInputs (q.relabel j) (w.relabel j) (r.relabel j) payload (r.relabel j) lifted
    exact exact_OpenAuxiliaryRootLeafCases leaf tag arity known xs (goal.relabel j) same accepted
      (beta guards β j Δ payload keep witness) (bottom guards β j Δ payload keep witness)
  · exact context

#print axioms exact_OpenTypedAuxiliaryThreeWays
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxThreeWaysProof
