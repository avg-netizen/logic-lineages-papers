module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarPlacementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel orderRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair boundBody boundReport)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSharedOwnScratchTargets (OwnOccurrence)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverArgumentMemoGrammarPlacementProof (actualArgumentMemoGrammarPlacement)
open NumberedWindowInternalCoverArgumentMemoBoundsProof (exact_OpenCoverArgumentMemoBounds)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveHead {β : Type} (s : Settings) (d w st terms args key : OTerm α)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (actual : OwnOccurrence s body Γ d w st terms args key) :
    OwnOccurrence s body Δ (d.relabel j) (w.relabel j) (st.relabel j) (terms.relabel j) (args.relabel j) (key.relabel j) := by
  have sc := renameInto actual.observedScope j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at sc
  have hit := renameInto actual.ownKey j Δ keep
  rw [graphRename] at hit
  exact ⟨sc,hit⟩

private theorem moveTail {β : Type} (s : Settings) (d w st terms args key : OTerm α)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (actual : ArgumentHit s body Γ d w st terms args key) :
    ArgumentHit s body Δ (d.relabel j) (w.relabel j) (st.relabel j) (terms.relabel j) (args.relabel j) (key.relabel j) := by
  have sc := renameInto actual.scope j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at sc
  have hit := renameInto actual.hit j Δ keep
  rw [graphRename] at hit
  exact ⟨sc,hit⟩

private theorem atWidth (s : Settings) (h a p dh wh dt wt w hs hts has ts tts tas : OTerm α) (goal : Formula α)
    (head : OwnOccurrence s body Γ dh wh hs hts has h)
    (tail : ArgumentHit s body Γ dt wt ts tts tas a)
    (bounds : Nonempty (Derivation body Γ (boundReport p dh dt wh wt w)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (codePair (p.relabel j) (suc (add (dh.relabel j) (dt.relabel j))) (w.relabel j))) →
      ArgumentHit s body Δ (suc (add (dh.relabel j) (dt.relabel j))) (w.relabel j) state terms args
        (rawCons (h.relabel j) (a.relabel j)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let H := headsTerm s α
  let K := typesTerm s α
  let d := add dh dt
  apply observationCases d H K w goal
  intro β j Δ mid mids mida keep before
  apply observationCases (suc (add (dh.relabel j) (dt.relabel j))) (headsTerm s β) (typesTerm s β)
    (w.relabel j) (goal.relabel j)
  intro γ g Ξ state terms args retain after
  let k := g ∘ j
  have both := keepThrough j g keep retain
  have h' := moveHead s dh wh hs hts has h k Ξ both head
  have a' := moveTail s dt wt ts tts tas a k Ξ both tail
  have old := renameInto before g Ξ retain
  simp only [observedRename,d,H,K,headsTerm,typesTerm,numeralRename,addRelabel,Term.relabel_relabel] at old
  simp only [headsTerm,typesTerm,numeralRename,sucRelabel,addRelabel,Term.relabel_relabel] at after
  have b' := renameInto bounds k Ξ both
  simp only [boundReport,conjunctionRename,pairRename,orderRename,sucRelabel,addRelabel] at b'
  have placed := actualArgumentMemoGrammarPlacement s (h.relabel k) (a.relabel k) (p.relabel k)
    (dh.relabel k) (wh.relabel k) (dt.relabel k) (wt.relabel k) (w.relabel k)
    (hs.relabel k) (hts.relabel k) (has.relabel k) (ts.relabel k) (tts.relabel k) (tas.relabel k)
    (mid.relabel g) (mids.relabel g) (mida.relabel g) state terms args h' a' b' old after
  obtain ⟨report⟩ := b'
  rw [formulaRelabelComposition j g goal]
  exact next γ k Ξ state terms args both ⟨Derivation.conjunctionLeft report⟩ placed

theorem exact_OpenCoverArgumentMemoGrammar : ExactOpenCoverArgumentMemoGrammar := by
  intro F s body α Γ h a p mh mt dh wh dt wt hs hts has ts tts tas goal paid head tail next
  obtain ⟨bounded⟩ := exact_OpenCoverArgumentMemoBounds F body α Γ h a p mh mt dh wh dt wt paid
  let j : α → α ⊕ Fin 1 := Sum.inl
  let A := boundBody p dh dt wh wt
  let Δ := A :: Γ.map weaken
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have keep (f : Formula α) (hf : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have row : Nonempty (Derivation body Δ (boundReport (p.relabel j) (dh.relabel j) (dt.relabel j)
      (wh.relabel j) (wt.relabel j) w)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h' := moveHead s dh wh hs hts has h j Δ keep head
  have a' := moveTail s dt wt ts tts tas a j Δ keep tail
  have found : Nonempty (Derivation body Δ (goal.relabel j)) := by
    apply atWidth s (h.relabel j) (a.relabel j) (p.relabel j) (dh.relabel j) (wh.relabel j)
      (dt.relabel j) (wt.relabel j) w (hs.relabel j) (hts.relabel j) (has.relabel j)
      (ts.relabel j) (tts.relabel j) (tas.relabel j) (goal.relabel j) h' a' row
    intro β g Ξ state terms args retain pair actual
    let k := g ∘ j
    simp only [Term.relabel_relabel] at pair actual
    rw [formulaRelabelComposition j g goal]
    exact next β k Ξ (w.relabel g) state terms args (keepThrough j g keep retain) pair actual
  obtain ⟨found⟩ := found
  exact ⟨Derivation.existentialElimination bounded found⟩

#print axioms exact_OpenCoverArgumentMemoGrammar

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarProof
