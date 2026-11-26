module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverInterfaceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves)
open NumberedWindowInternalLiteralRoundObserverSyntaxProof (observeRename)
open NumberedWindowInternalSparseDirectedSeen (edgeTape acceptEdge)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeTwo compositeThree compareEvaluation)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def atEndpoint (O : Program 3) (i : Fin 4) : Program 4 :=
  .composition O (Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (.projection i) Fin.elim0)))

def observerCheck (O : Program 3) : Program 4 :=
  .composition compareNumbers (Fin.cons (atEndpoint O 2) (Fin.cons (atEndpoint O 3) Fin.elim0))

/-- Add an actual comparison of the original physical observer's
values at the two endpoints. No proof is transported merely because
this checker can later be numerically calibrated to an older one. -/
def enrichedEdge (E : Program 4) (O : Program 3) : Program 4 :=
  conjunction E (observerCheck O)

private theorem checkValue (O : Program 3) (ctx ty a b : Nat) :
    evaluate (observerCheck O) (List.Vector.ofFn (edgeTape ctx ty a b)) =
      if evaluate O (ctx ::ᵥ ty ::ᵥ a ::ᵥ nil) = evaluate O (ctx ::ᵥ ty ::ᵥ b ::ᵥ nil) then 1 else 0 := by
  rw [observerCheck,compositeTwo,atEndpoint,atEndpoint,compositeThree,compositeThree]
  change evaluate compareNumbers (evaluate O (ctx ::ᵥ ty ::ᵥ a ::ᵥ nil) ::ᵥ
    evaluate O (ctx ::ᵥ ty ::ᵥ b ::ᵥ nil) ::ᵥ nil) = _
  exact compareEvaluation _ _

theorem exact_EnrichedEdgeBit (E : Program 4) (O : Program 3)
    (stable : ∀ ctx ty a b, exactEdgeBit E ctx ty a b = true →
      evaluate O (ctx ::ᵥ ty ::ᵥ a ::ᵥ nil) = evaluate O (ctx ::ᵥ ty ::ᵥ b ::ᵥ nil)) :
    exactEdgeBit (enrichedEdge E O) = exactEdgeBit E := by
  funext ctx ty a b
  unfold exactEdgeBit enrichedEdge
  rw [actualConjunctionEvaluation,checkValue]
  by_cases h : evaluate E (List.Vector.ofFn (edgeTape ctx ty a b)) = 1
  · have same := stable ctx ty a b (by simp [exactEdgeBit,h])
    simp [h,same]
  · simp [h]

private theorem endpointRead (O : Program 3) (i : Fin 4) (ctx ty a b value : OTerm α)
    (h : D B Γ (observe O ctx ty ((![ctx,ty,a,b] : Fin 4 → OTerm α) i) value)) :
    D B Γ (programGraph (atEndpoint O i) value ![ctx,ty,a,b]) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a,b]
  apply compositionValue O (Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (.projection i) Fin.elim0)))
    value xs ![ctx,ty,xs i] h
  exact fun j => Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue i xs) (fun e => Fin.elim0 e))) j

theorem exact_OpenEnrichedEdgeEqual (E : Program 4) (O : Program 3) (ctx ty a b x y : OTerm α)
    (edge : D B Γ (acceptEdge (enrichedEdge E O) ctx ty a b))
    (left : D B Γ (observe O ctx ty a x)) (right : D B Γ (observe O ctx ty b y)) :
    D B Γ (eqn x y) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a,b]
  obtain ⟨both⟩ := conjunctionRecover E (observerCheck O) xs edge
  have compare : D B Γ (programGraph (observerCheck O) (suc z) xs) := ⟨Derivation.conjunctionRight both⟩
  unfold observerCheck at compare
  rw [exact_DispatchControlAST.2.2.2.1] at compare
  have tested := compositionRecover equalityTest
    (Fin.cons (atEndpoint O 2) (Fin.cons (atEndpoint O 3) Fin.elim0))
    (suc z) xs (Fin.cons x (Fin.cons y Fin.elim0)) compare
    (fun j => Fin.cases (endpointRead O 2 ctx ty a b x left)
      (Fin.cases (endpointRead O 3 ctx ty a b y right) (fun e => Fin.elim0 e)) j)
  exact equalityOfAcceptance x y tested

theorem exact_OpenEnrichedEdgeBase (E : Program 4) (O : Program 3) (ctx ty a b : OTerm α)
    (edge : D B Γ (acceptEdge (enrichedEdge E O) ctx ty a b)) :
    D B Γ (acceptEdge E ctx ty a b) := by
  obtain ⟨parts⟩ := conjunctionRecover E (observerCheck O) ![ctx,ty,a,b] edge
  exact ⟨Derivation.conjunctionLeft parts⟩

theorem exact_OpenEnrichedEdgeObservation (E : Program 4) (O : Program 3) :
    Preserves (enrichedEdge E O) O := by
  intro B α Γ ctx ty a b x edge left
  apply programCases O ![ctx,ty,b] (observe O ctx ty b x)
  intro β j Δ y keep right
  rw [observeRename O]
  rw [tripleInputsRename] at right
  have l := renameInto left j Δ keep
  rw [observeRename O] at l
  have physical := renameInto edge j Δ keep
  simp only [acceptEdge,edgeTape,programRename,quadInputsRename,sucRelabel,zRelabel] at physical
  obtain ⟨same⟩ := exact_OpenEnrichedEdgeEqual E O (ctx.relabel j) (ty.relabel j)
    (a.relabel j) (b.relabel j) (x.relabel j) y physical l right
  exact outputTransport O y (x.relabel j) ![ctx.relabel j,ty.relabel j,b.relabel j] ⟨symm same⟩ right

/-- The enrichment checks may be recreated from the physical original
edge and two actual equal-value observations; useful for reversal. -/
theorem exact_OpenEnrichedEdgeIntro (E : Program 4) (O : Program 3) (ctx ty a b x y : OTerm α)
    (edge : D B Γ (acceptEdge E ctx ty a b))
    (left : D B Γ (observe O ctx ty a x)) (right : D B Γ (observe O ctx ty b y))
    (same : D B Γ (eqn x y)) :
    D B Γ (acceptEdge (enrichedEdge E O) ctx ty a b) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a,b]
  have comparison : D B Γ (programGraph (observerCheck O) (suc z) xs) := by
    unfold observerCheck
    rw [exact_DispatchControlAST.2.2.2.1]
    apply compositionValue equalityTest (Fin.cons (atEndpoint O 2) (Fin.cons (atEndpoint O 3) Fin.elim0))
      (suc z) xs (Fin.cons x (Fin.cons y Fin.elim0)) (equalityOfEqual x y same)
    exact fun i => Fin.cases (endpointRead O 2 ctx ty a b x left)
      (Fin.cases (endpointRead O 3 ctx ty a b y right) (fun e => Fin.elim0 e)) i
  exact conjunctionAccept E (observerCheck O) xs edge comparison

#print axioms exact_EnrichedEdgeBit
#print axioms exact_OpenEnrichedEdgeEqual
#print axioms exact_OpenEnrichedEdgeBase
#print axioms exact_OpenEnrichedEdgeObservation
#print axioms exact_OpenEnrichedEdgeIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
