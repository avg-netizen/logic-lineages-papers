module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountCasesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapAcceptedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountInductionTargets (project compared)
open NumberedWindowInternalProjectedCountInductionProof (exact_OpenProjectedCount)
open NumberedWindowInternalProjectedCountInductionSyntaxProof (projectRename)
open NumberedWindowInternalOriginScanInductionSyntaxProof (filterRename)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalDirectTargetMapAcceptedProof (exact_OpenAcceptedScanProjectionCases)
open NumberedWindowInternalProjectedCountCasesTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem relocate {β : Type} {Δ : List (Formula β)}
    {r : Program 3} {a pool u v rl rr full : OTerm α}
    (input : Inputs r B Γ a pool u v rl rr full) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Inputs r B Δ (a.relabel j) (pool.relabel j) (u.relabel j) (v.relabel j)
      (rl.relabel j) (rr.relabel j) (full.relabel j) := by
  let move := fun {f} (h : D B Γ f) => renameInto h j Δ keep
  exact ⟨by simpa only [filterRename] using move input.filteredLeft,
    by simpa only [filterRename] using move input.filteredRight,
    by simpa only [loopRename] using move input.acceptedLeft,
    by simpa only [loopRename] using move input.acceptedRight,
    by simpa only [projectRename] using move input.allProjected⟩

private theorem through {β γ : Type} {Δ : List (Formula β)} {Ω : List (Formula γ)}
    (j : α → β) (k : β → γ)
    (a : ∀ f ∈ Γ, f.relabel j ∈ Δ) (b : ∀ f ∈ Δ, f.relabel k ∈ Ω) :
    ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ω := by
  intro f hf
  rw [← formulaRelabelComposition]
  exact b _ (a f hf)

theorem exact_OpenProjectedCountCases : ExactOpenProjectedCountCases := by
  intro r B α Γ rows pool outL outR removedL removedR full goal input k
  apply exact_OpenAcceptedScanProjectionCases r outL removedL goal input.acceptedLeft
  intro β j Δ pL keep hL
  have around := relocate input j keep
  apply exact_OpenAcceptedScanProjectionCases r (outR.relabel j) (removedR.relabel j)
    (goal.relabel j) around.acceptedRight
  intro γ i Ω pR keep' hR
  rw [formulaRelabelComposition]
  let ji := i ∘ j
  have saved := relocate input ji (through j i keep keep')
  have left : D B Ω (project (pL.relabel i) (outL.relabel ji)) := by
    have p := renameInto hL i Ω keep'
    have q : D B Ω ((project pL (outL.relabel j)).relabel i) := p
    simpa only [projectRename,Term.relabel_relabel,ji] using q
  have right : D B Ω (project pR (outR.relabel ji)) := by
    simpa only [Term.relabel_relabel,ji] using hR
  apply programCases append ![pL.relabel i,pR] (goal.relabel ji)
  intro δ l Ξ joined keep'' joinedView
  rw [binaryInputsRename] at joinedView
  have act := relocate saved l keep''
  have aL : D B Ξ (project ((pL.relabel i).relabel l) ((outL.relabel ji).relabel l)) := by
    simpa only [projectRename] using renameInto left l Ξ keep''
  have aR : D B Ξ (project (pR.relabel l) ((outR.relabel ji).relabel l)) := by
    simpa only [projectRename] using renameInto right l Ξ keep''
  obtain ⟨fL⟩ := act.filteredLeft
  obtain ⟨fR⟩ := act.filteredRight
  obtain ⟨whole⟩ := act.allProjected
  obtain ⟨l'⟩ := aL
  obtain ⟨r'⟩ := aR
  obtain ⟨j'⟩ := joinedView
  have all := exact_OpenProjectedCount B δ Ξ ((rows.relabel ji).relabel l) ((pool.relabel ji).relabel l)
    ((outL.relabel ji).relabel l) ((outR.relabel ji).relabel l) ((full.relabel ji).relabel l)
    ((pL.relabel i).relabel l) (pR.relabel l) joined
    ⟨Derivation.conjunctionIntroduction fL (Derivation.conjunctionIntroduction fR
      (Derivation.conjunctionIntroduction whole (Derivation.conjunctionIntroduction l'
        (Derivation.conjunctionIntroduction r' j'))))⟩
  rw [formulaRelabelComposition]
  exact k δ (l ∘ ji) Ξ ((pL.relabel i).relabel l) (pR.relabel l) joined
    (through ji l (through j i keep keep') keep'')
    (by simpa only [Term.relabel_relabel] using (show Nonempty _ from ⟨l'⟩))
    (by simpa only [Term.relabel_relabel] using (show Nonempty _ from ⟨r'⟩))
    ⟨j'⟩ (by simpa only [Term.relabel_relabel] using all)

#print axioms exact_OpenProjectedCountCases

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountCasesProof
