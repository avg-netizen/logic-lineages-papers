module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnFixedPointProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserversProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedWindowEndpointsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralLeastOnFixedPointProof
open NumberedWindowInternalLiteralEnrichedEdgeProof (exact_OpenEnrichedEdgeBase)
open NumberedWindowInternalLiteralEdgeObserversProof (withObservers)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenOriginalWindowEndpoints (X : Program 2) (W : Program 3) :
    WindowEndpoints W (edge4 X W) := by
  intro B α Γ ctx ty a b held
  obtain ⟨rule⟩ := exact_OpenPackedScalarEdge X W B α Γ ctx ty a b
  obtain ⟨edge⟩ := held
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft rule) edge
  let pair := Derivation.conjunctionRight calls
  exact ⟨⟨Derivation.conjunctionLeft pair⟩,⟨Derivation.conjunctionRight pair⟩⟩

theorem exact_OpenEdgeWithoutObservers (E : Program 4) (ss : List (Program 3)) (ctx ty a b : OTerm α)
    (held : D B Γ (acceptEdge (withObservers E ss) ctx ty a b)) :
    D B Γ (acceptEdge E ctx ty a b) := by
  induction ss with
  | nil => exact held
  | cons O tail ih => exact ih (exact_OpenEnrichedEdgeBase (withObservers E tail) O ctx ty a b held)

theorem exact_OpenSuiteWindowEndpoints (W : Program 3) (E : Program 4) (ss : List (Program 3))
    (before : WindowEndpoints W E) : WindowEndpoints W (withObservers E ss) := by
  intro B α Γ ctx ty a b held
  exact before B α Γ ctx ty a b (exact_OpenEdgeWithoutObservers E ss ctx ty a b held)

theorem exact_OpenCoveredWindowEndpoints (C : Program 3) (s : Settings) (W : Program 3) (E : Program 4)
    (before : WindowEndpoints W E)
    (cover : ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed : OTerm α),
      D B Γ (windowAt W ctx ty seed) → D B Γ (coverageReport C s ctx seed)) :
    CoveredEndpoints C s E := by
  intro B α Γ ctx ty a b held
  obtain ⟨left,right⟩ := before B α Γ ctx ty a b held
  exact ⟨cover B α Γ ctx ty a left,cover B α Γ ctx ty b right⟩

#print axioms exact_OpenOriginalWindowEndpoints
#print axioms exact_OpenEdgeWithoutObservers
#print axioms exact_OpenSuiteWindowEndpoints
#print axioms exact_OpenCoveredWindowEndpoints
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedWindowEndpointsProof
