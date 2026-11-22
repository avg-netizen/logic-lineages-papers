module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureArgumentProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchOrdinaryProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalCoverHeadDispatchTargets (OrdinaryNoHeadFacts)
open NumberedWindowInternalCoverOrdinaryMeasureArgumentProof (exact_OpenCoverOrdinaryArgumentPair)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasuredPrograms numberedMeasureBase)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough moveParentPair moveWeak)
open NumberedWindowInternalCoverMeasuredDispatchTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenMeasuredOrdinaryFacts (V TV M A : Program 1) (B : Program 2) (T : Program 1)
    (s : Settings) (raw p vertices ctx result h a : OTerm α) (goal : Formula α)
    (needs : MeasuredRemaining (numberedMeasuredPrograms s V TV M A B T) A s body)
    (row : PackedRow (numberedMeasuredPrograms s V TV M A B T) s body Γ raw (ordinaryKey h a)
      p vertices ctx result 4 [h,a]) :
    Supplies body Γ goal (fun β j Δ => OrdinaryNoHeadFacts s body Δ (p.relabel j) (a.relabel j)) := by
  intro next
  apply exact_OpenCoverOrdinaryArgumentPair (numberedMeasureBase M A) A body α Γ h a p goal row.data.parent.measured
  intro β j Δ m d w keep args pair parentPair depth width
  apply needs.ordinary α Γ raw p vertices ctx result h a goal row β j Δ m d w keep args pair
  intro γ g Ξ retain actual
  obtain ⟨state,terms,observed,scope,hit⟩ := actual
  let jg := g ∘ j
  have both := keepThrough j g keep retain
  have sameP := moveParentPair g retain (p.relabel j) d w parentPair
  simp only [Term.relabel_relabel] at sameP
  have cd := moveWeak g retain d d depth
  have cw := moveWeak g retain w w width
  rw [formulaRelabelComposition j g goal]
  exact next γ jg Ξ both ⟨d.relabel g,w.relabel g,d.relabel g,w.relabel g,state,terms,observed,
    sameP,⟨scope,hit,cd,cw⟩⟩

#print axioms exact_OpenMeasuredOrdinaryFacts

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchOrdinaryProof
