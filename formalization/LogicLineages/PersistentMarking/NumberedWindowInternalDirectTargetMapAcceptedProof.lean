module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapAcceptedConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapAcceptedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalDirectTargetMapLocalIntroProof (exact_OpenTargetProjectionNil)
open NumberedWindowInternalDirectTargetMapAcceptedConsProof (exact_AcceptedScanProjectCons)
open NumberedWindowInternalDirectTargetMapIntroSyntaxProof (motiveCode motiveIndex projectionIntro projectionCases)
open NumberedWindowInternalDirectTargetMapIntroTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilAt (r : Program 3) (removed : OTerm α) : D B Γ (atRows r z removed) := by
  let S := loopAccept r z removed
  obtain ⟨h⟩ := projectionIntro z z (exact_OpenTargetProjectionNil B α (S :: Γ))
  exact ⟨Derivation.implicationIntroduction h⟩

private theorem consAt (r : Program 3) (rows row tail removed : OTerm α)
    (cell : D B Γ (consGraph rows row tail)) (ih : D B Γ (atRows r tail removed)) :
    D B Γ (atRows r rows removed) := by
  let S := loopAccept r rows removed
  have original : D B (S :: Γ) S := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := exact_AcceptedScanProjectCons r rows row tail removed (withHyp cell S)
    original (withHyp ih S)
  exact ⟨Derivation.implicationIntroduction h⟩

private theorem constructorsAt (r : Program 3) (removed : OTerm α) :
    D B Γ (constructors (motive r removed)) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (motive r removed))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let inherited := atRows r t (removed.relabel j)
  let G := Γ.map (fun p => p.relabel j)
  let Δ := inherited :: C :: G
  change D B G (C.imp ((atIndex (motive r removed) 2).imp (atIndex (motive r removed) 0)))
  simp only [motiveIndex]
  obtain ⟨h⟩ := consAt (B := B) (Γ := Δ) r n h t (removed.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem exact_OpenAcceptedScanHasProjection : ExactOpenAcceptedScanHasProjection := by
  intro r B α Γ rows removed
  have base : D B Γ (atCode (motive r removed) z) := by
    rw [motiveCode]
    exact nilAt r removed
  obtain ⟨b⟩ := base
  obtain ⟨s⟩ := constructorsAt (B := B) (Γ := Γ) r removed
  have pack : D B Γ (premises (motive r removed)) :=
    ⟨Derivation.conjunctionIntroduction b s⟩
  have all := actualOriginalListInductionAtCode B α Γ (motive r removed) rows pack
  rw [motiveCode] at all
  exact all

/-- Convenient original object elimination at an actual accepted scan. -/
theorem exact_OpenAcceptedScanProjectionCases (r : Program 3) (rows removed : OTerm α)
    (goal : Formula α) (accepted : D B Γ (loopAccept r rows removed))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      D B Δ (unary scratchTargets (suc out) (rows.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  obtain ⟨h⟩ := exact_OpenAcceptedScanHasProjection r B α Γ rows removed
  obtain ⟨a⟩ := accepted
  exact projectionCases rows goal ⟨Derivation.implicationElimination h a⟩ next

#print axioms exact_OpenAcceptedScanHasProjection
#print axioms exact_OpenAcceptedScanProjectionCases

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapAcceptedProof
