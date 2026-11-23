module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedParentStageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedParentStageBoundsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverRename)
open NumberedWindowInternalCoverGrammarStageTargets (termsGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm installedCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundBody boundReport)
open NumberedWindowInternalChosenAuxMeasureObservedTargets (parentMeasureAndBounds)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename)
open NumberedWindowInternalMeasuredUnrestrictedParentStageProof
  (StageTermTransport stageTermsRename exact_OpenUnrestrictedParentOwnAtBounds)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Use the real chosen measurement report and its one bound witness.
Neither the common predecessor depth nor either width comparison is
assumed. Open transport on the installed same grammar remains explicit. -/
theorem exact_OpenUnrestrictedMeasuredParentOwnAtStages
    (V baseM : Program 1) (P : Program 5) (A : Program 2) (s : Settings)
    (dom cod fn arg p df bf da ba fs ats : OTerm α)
    (lift : StageTermTransport P A s)
    (valid : Nonempty (Derivation B Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg))))
    (parent : Nonempty (Derivation B Γ (parentMeasureAndBounds baseM dom cod fn arg p df da bf ba)))
    (fnStage : Nonempty (Derivation B Γ (termsGraph P A fs df (headsTerm s α) (typesTerm s α) bf)))
    (argStage : Nonempty (Derivation B Γ (termsGraph P A ats da (headsTerm s α) (typesTerm s α) ba)))
    (domIn : Nonempty (Derivation B Γ (memberGraph (typesTerm s α) dom)))
    (codIn : Nonempty (Derivation B Γ (memberGraph (typesTerm s α) cod)))
    (fnIn : Nonempty (Derivation B Γ (memberGraph fs fn)))
    (argIn : Nonempty (Derivation B Γ (memberGraph ats arg))) :
    Nonempty (Derivation B Γ (occursInCover (installedCover V (selectedMeasure (measureUpdate baseM chosenCombine)) P A) s
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn arg))) := by
  obtain ⟨pData⟩ := parent
  let j : α → α ⊕ Fin 1 := Sum.inl
  let A' := boundBody p df da bf ba
  let Δ := A' :: Γ.map weaken
  let b : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have row : Derivation B Δ
    (boundReport (p.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j) b) :=
    Derivation.hypothesis List.mem_cons_self
  have offsets := Derivation.conjunctionRight row
  have depths := Derivation.conjunctionLeft offsets
  have widths := Derivation.conjunctionRight offsets
  have valid' := renameInto valid j Δ keep
  have measured := renameInto (Nonempty.intro (Derivation.conjunctionLeft pData)) j Δ keep
  have fstage := renameInto fnStage j Δ keep
  have astage := renameInto argStage j Δ keep
  have hd := renameInto domIn j Δ keep
  have hc := renameInto codIn j Δ keep
  have hf := renameInto fnIn j Δ keep
  have ha := renameInto argIn j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at valid'
  simp only [measureRename,auxiliaryRename] at measured
  rw [stageTermsRename] at fstage astage
  simp only [graphRename,typesTerm,numeralRename] at hd hc
  rw [graphRename] at hf ha
  let d := add (df.relabel j) (da.relabel j)
  have hit := exact_OpenUnrestrictedParentOwnAtBounds V (selectedMeasure (measureUpdate baseM chosenCombine))
    P A s (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) (p.relabel j) d b
    (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j) (fs.relabel j) (ats.relabel j)
    lift valid' measured ⟨Derivation.conjunctionLeft row⟩ fstage astage
    ⟨Derivation.conjunctionLeft depths⟩ ⟨Derivation.conjunctionRight depths⟩
    ⟨Derivation.conjunctionLeft widths⟩ ⟨Derivation.conjunctionRight widths⟩ hd hc hf ha
  rw [← auxiliaryRename,← coverRename] at hit
  obtain ⟨found⟩ := hit
  exact ⟨Derivation.existentialElimination (Derivation.conjunctionRight pData) found⟩

#print axioms exact_OpenUnrestrictedMeasuredParentOwnAtStages
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedParentStageBoundsProof
