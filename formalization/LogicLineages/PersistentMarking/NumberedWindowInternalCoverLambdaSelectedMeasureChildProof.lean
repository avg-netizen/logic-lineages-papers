module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureLiteralProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureChildProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename moveReport)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasure)
open NumberedWindowInternalCoverLambdaSelectedMeasureTargets
open NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof (codePairCases)
open NumberedWindowInternalCoverLambdaSelectedMeasureLiteralProof (exact_OpenCoverLambdaSelectedMeasureAtCoordinates)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atChild (M : Program 1) (ty q mc p : OTerm α) (goal : Formula α)
    (parent : Nonempty (Derivation body Γ (unary (lambdaMeasure M) p (lambdaTerm ty q))))
    (child : Nonempty (Derivation body Γ (unary (lambdaMeasure M) mc q)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old d w : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      LambdaMeasureEvidence M body Δ (ty.relabel j) (q.relabel j) old (mc.relabel j) (p.relabel j) d w →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply codePairCases mc goal
  intro β j Δ d w keep code
  have parent' := moveReport j Δ keep (lambdaMeasure M) p (lambdaTerm ty q) parent
  simp only [lambdaTerm,namedRename] at parent'
  have child' := moveReport j Δ keep (lambdaMeasure M) mc q child
  apply exact_OpenCoverLambdaSelectedMeasureAtCoordinates M body β Δ
    (ty.relabel j) (q.relabel j) (mc.relabel j) (p.relabel j) d w (goal.relabel j) parent' child' code
  intro γ k Ξ old retain row
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ old (d.relabel k) (w.relabel k) both row

theorem exact_OpenCoverLambdaSelectedMeasure : ExactOpenCoverLambdaSelectedMeasure := by
  intro M body α Γ ty q p goal parent next
  apply programCases (lambdaMeasure M) ![q] goal
  intro β j Δ mc keep child
  rw [inputsRename] at child
  have parent' := moveReport j Δ keep (lambdaMeasure M) p (lambdaTerm ty q) parent
  simp only [lambdaTerm,namedRename] at parent'
  apply atChild M (ty.relabel j) (q.relabel j) mc (p.relabel j) (goal.relabel j) parent' child
  intro γ k Ξ old d w retain row
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ old (mc.relabel k) d w both row

#print axioms exact_OpenCoverLambdaSelectedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureChildProof
