module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowSelectedProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchNumberedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalCoverHeadDispatchTargets (NumberedNoHeadFacts)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasuredPrograms)
open NumberedWindowInternalCoverNumberedMeasureSelectedParentProof (exact_OpenCoverNumberedMeasuredArgs)
open NumberedWindowInternalCoverNumberedTypeWindowSelectedProof (exact_OpenCoverNumberedTypeWindow)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough moveParentPair moveWeak moveStoredK)
open NumberedWindowInternalCoverMeasuredDispatchTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenMeasuredNumberedFacts (V TV M A : Program 1) (B : Program 2) (T : Program 1)
    (s : Settings) (raw p vertices ctx result h ty k l r : OTerm α) (goal : Formula α)
    (needs : MeasuredRemaining (numberedMeasuredPrograms s V TV M A B T) A s body)
    (row : PackedRow (numberedMeasuredPrograms s V TV M A B T) s body Γ raw (numberedTerm h ty k l r)
      p vertices ctx result 5 [h,ty,k,l,r]) :
    Supplies body Γ goal (fun β j Δ => NumberedNoHeadFacts s body Δ
      (p.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)) := by
  intro next
  have storedK := exact_OpenCoverNumberedTypeWindow s B T body α Γ ctx h ty k l r result row.data.typed
  apply exact_OpenCoverNumberedMeasuredArgs M A body α Γ h ty k l r p goal row.data.parent.measured
  intro β j Δ ml mr dl dr wl wr width keep actual
  apply needs.numbered α Γ raw p vertices ctx result h ty k l r goal row β j Δ ml mr dl dr wl wr width keep actual
  intro γ g Ξ retain arguments
  obtain ⟨ls,lt,la,lScope,lHit⟩ := arguments.1
  obtain ⟨rs,rt,ra,rScope,rHit⟩ := arguments.2
  let jg := g ∘ j
  let depth := add dl dr
  have both := keepThrough j g keep retain
  have sameP := moveParentPair g retain (p.relabel j) depth width actual.paid.parent
  simp only [Term.relabel_relabel] at sameP
  have ld := moveWeak g retain dl depth actual.paid.leftDepth
  have rd := moveWeak g retain dr depth actual.paid.rightDepth
  have lw := moveWeak g retain wl width actual.paid.leftWidth
  have rwid := moveWeak g retain wr width actual.paid.rightWidth
  have id := moveWeak g retain (k.relabel j) width actual.paid.storedNumeral
  simp only [Term.relabel_relabel] at id
  rw [formulaRelabelComposition j g goal]
  exact next γ jg Ξ both ⟨depth.relabel g,width.relabel g,dl.relabel g,wl.relabel g,ls,lt,la,
    dr.relabel g,wr.relabel g,rs,rt,ra,sameP,⟨lScope,lHit,ld,lw⟩,⟨rScope,rHit,rd,rwid⟩,
    moveStoredK s jg both ty storedK,id⟩

#print axioms exact_OpenMeasuredNumberedFacts

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchNumberedProof
