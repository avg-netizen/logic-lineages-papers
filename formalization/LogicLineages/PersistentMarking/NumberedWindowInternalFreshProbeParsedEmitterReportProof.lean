module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterReportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)

def rawPrograms (bound : Program 1) : Fin 6 → Program 1 :=
  ![rawContext,rawResult,rawDomain,rawCodomain,rawLeast,applyUnary bound rawLeast]

private def reporter (bound : Program 1) : Program 1 :=
  .composition (zeroAt 6) (rawPrograms bound)

/-- A proof-local original composition whose six *actual program*
outputs are obtained by genuine original Program graph totality. The
dummy outer output is discarded; the same q is passed to all calls. -/
theorem reportCases {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (bound : Program 1) (q : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ys : Fin 6 → OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      (∀ i, Nonempty (Derivation body Δ (programGraph (rawPrograms bound i) (ys i) ![q.relabel j]))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases (reporter bound) ![q] goal
  intro β j Δ y hj hy
  rw [unaryRename] at hy
  apply programCompositionCases (zeroAt 6) (rawPrograms bound) y ![q.relabel j] (goal.relabel j) hy
  intro γ l ys Θ hl _ reports
  rw [formulaRelabelComposition]
  apply k γ (l ∘ j) Θ ys
  · intro f hf
    rw [← formulaRelabelComposition]
    exact hl (f.relabel j) (hj f hf)
  · intro i
    have h := reports i
    rw [unaryRename,Term.relabel_relabel] at h
    exact h

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterReportProof
