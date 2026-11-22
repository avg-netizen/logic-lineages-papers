module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalCoverFittedInductionDispatchTargets (Remaining)
open NumberedWindowInternalCoverFittedInductionDispatchProof (exact_OpenCoverFittedInductionDispatch)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase)
open NumberedWindowInternalCoverHeadWindowSelectedProof (exact_OpenCoverHeadFittedWindow)
open NumberedWindowInternalCoverHeadDispatchTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem moveHead (s : Settings) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) (h : OTerm α)
    (actual : Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h))) :
    Nonempty (Derivation body Δ (memberGraph (headsTerm s β) (h.relabel j))) := by
  have same := renameInto actual j Δ keep
  simpa only [graphRename,headsTerm,numeralRename] using same

private theorem ordinaryFacts (V TV M : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (raw p vertices ctx result h a : OTerm α) (goal : Formula α)
    (row : PackedRow (headPrograms s V TV M B T) s body Γ raw (ordinaryKey h a)
      p vertices ctx result 4 [h,a])
    (remaining : Supplies body Γ goal
      (fun β j Δ => OrdinaryNoHeadFacts s body Δ (p.relabel j) (a.relabel j))) :
    Supplies body Γ goal (fun β j Δ => OrdinaryFacts s body Δ (p.relabel j) (h.relabel j) (a.relabel j)) := by
  intro next
  have actual := exact_OpenCoverHeadFittedWindow false s B T body α Γ ctx h result [a] rfl row.data.typed
  apply remaining
  intro γ j Ξ keep facts
  obtain ⟨d,width,da,wa,state,terms,args,mp,occ⟩ := facts
  exact next γ j Ξ keep ⟨d,width,da,wa,state,terms,args,mp,occ,moveHead s j keep h actual⟩

private theorem numberedFacts (V TV M : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (raw p vertices ctx result h ty k l r : OTerm α) (goal : Formula α)
    (row : PackedRow (headPrograms s V TV M B T) s body Γ raw (numberedTerm h ty k l r)
      p vertices ctx result 5 [h,ty,k,l,r])
    (remaining : Supplies body Γ goal
      (fun β j Δ => NumberedNoHeadFacts s body Δ
        (p.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j))) :
    Supplies body Γ goal (fun β j Δ => NumberedFacts s body Δ
      (p.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)) := by
  intro next
  have actual := exact_OpenCoverHeadFittedWindow true s B T body α Γ ctx h result [ty,k,l,r] rfl row.data.typed
  apply remaining
  intro γ j Ξ keep facts
  obtain ⟨d,width,dl,wl,ls,lt,la,dr,wr,rs,rt,ra,mp,left,right,kt,ki⟩ := facts
  exact next γ j Ξ keep ⟨d,width,dl,wl,ls,lt,la,dr,wr,rs,rt,ra,mp,left,right,moveHead s j keep h actual,kt,ki⟩

theorem exact_OpenCoverHeadFittedDispatch : ExactOpenCoverHeadFittedDispatch := by
  intro V TV M B T s body α Γ raw p vertices ctx result P remain physical
  have needed : Remaining P s body := {
    lambdaBody := remain.lambdaBody
    ordinary := fun _ _ q m out x y h a goal row =>
      ordinaryFacts V TV M B T s q m out x y h a goal row (remain.ordinary _ _ q m out x y h a goal row)
    numbered := fun _ _ q m out x y h t k l r goal row =>
      numberedFacts V TV M B T s q m out x y h t k l r goal row (remain.numbered _ _ q m out x y h t k l r goal row)
  }
  exact exact_OpenCoverFittedInductionDispatch V TV M (grammarHeadBase s B) T s body α Γ raw p vertices ctx result needed physical

#print axioms exact_OpenCoverHeadFittedDispatch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchProof
