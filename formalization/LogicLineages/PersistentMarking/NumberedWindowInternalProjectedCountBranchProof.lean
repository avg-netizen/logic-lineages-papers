module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPairedProjectedConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalPairedProjectedConsProof (exact_OpenPairedProjectedCons)
open NumberedWindowInternalOriginScanInductionSyntaxProof (filterRename)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountInductionTargets (atRows compared project)
open NumberedWindowInternalProjectedCountInductionSyntaxProof
  (atRowsRename comparedRename projectRename appendedRename applyAtRows)
open NumberedWindowInternalProjectedCountBranchTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem renameSide {β : Type} (side : Bool) (u v w : OTerm α) (j : α → β) :
    (sidedAppend side u v w).relabel j =
      sidedAppend side (u.relabel j) (v.relabel j) (w.relabel j) := by
  cases side <;> simp only [sidedAppend, Bool.false_eq_true, if_false, if_true, appendedRename]

private theorem packTail (side : Bool)
    (tail pool chosen idle wholeProj chosenProj idleProj priorAppend : OTerm α)
    (l : D B Γ (filterGraph side chosen tail pool))
    (r : D B Γ (filterGraph (!side) idle tail pool))
    (ap : D B Γ (project wholeProj tail))
    (lp : D B Γ (project chosenProj chosen))
    (rp : D B Γ (project idleProj idle))
    (j : D B Γ (sidedAppend side priorAppend chosenProj idleProj))
    (ih : D B Γ (atRows tail pool)) : D B Γ (compared wholeProj priorAppend) := by
  obtain ⟨lf⟩ := l
  obtain ⟨rf⟩ := r
  obtain ⟨main⟩ := ap
  obtain ⟨fromL⟩ := lp
  obtain ⟨fromR⟩ := rp
  obtain ⟨joined⟩ := j
  cases side
  · exact applyAtRows tail pool idle chosen wholeProj idleProj chosenProj priorAppend ih
      ⟨Derivation.conjunctionIntroduction rf (Derivation.conjunctionIntroduction lf
        (Derivation.conjunctionIntroduction main (Derivation.conjunctionIntroduction fromR
          (Derivation.conjunctionIntroduction fromL joined))))⟩
  · exact applyAtRows tail pool chosen idle wholeProj chosenProj idleProj priorAppend ih
      ⟨Derivation.conjunctionIntroduction lf (Derivation.conjunctionIntroduction rf
        (Derivation.conjunctionIntroduction main (Derivation.conjunctionIntroduction fromL
          (Derivation.conjunctionIntroduction fromR joined))))⟩

private theorem appendCases (side : Bool) (chosen idle : OTerm α) (goal : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (o : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (sidedAppend side o (chosen.relabel j) (idle.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  cases side
  · apply programCases append ![idle,chosen] goal
    intro β j Δ o keep h
    rw [binaryInputsRename] at h
    exact k β j Δ o keep h
  · apply programCases append ![chosen,idle] goal
    intro β j Δ o keep h
    rw [binaryInputsRename] at h
    exact k β j Δ o keep h

private theorem assemble (side : Bool) (law : SideCountCongruence side)
    (tail pool chosen idle oldProj chosenProj idleProj allOut sideOut joined key : OTerm α)
    (fChosen : D B Γ (filterGraph side chosen tail pool))
    (fIdle : D B Γ (filterGraph (!side) idle tail pool))
    (allTail : D B Γ (project oldProj tail))
    (chosenTail : D B Γ (project chosenProj chosen))
    (otherMap : D B Γ (project idleProj idle))
    (orig : D B Γ (consGraph allOut key oldProj))
    (kept : D B Γ (consGraph sideOut key chosenProj))
    (newJoin : D B Γ (sidedAppend side joined sideOut idleProj))
    (ih : D B Γ (atRows tail pool)) : D B Γ (compared allOut joined) := by
  apply appendCases side chosenProj idleProj (compared allOut joined)
  intro β j Δ tailJoin keep oldJoin
  have fromChosen := renameInto fChosen j Δ keep
  have fromIdle := renameInto fIdle j Δ keep
  have atTail := renameInto allTail j Δ keep
  have atChosen := renameInto chosenTail j Δ keep
  have atOther := renameInto otherMap j Δ keep
  have orig' := renameInto orig j Δ keep
  have kept' := renameInto kept j Δ keep
  have newJoin' := renameInto newJoin j Δ keep
  have ih' := renameInto ih j Δ keep
  rw [filterRename] at fromChosen fromIdle
  rw [projectRename] at atTail atChosen atOther
  rw [consGraphRename] at orig' kept'
  rw [renameSide] at newJoin'
  rw [atRowsRename] at ih'
  rw [comparedRename]
  have tailCount := packTail side (tail.relabel j) (pool.relabel j) (chosen.relabel j) (idle.relabel j)
    (oldProj.relabel j) (chosenProj.relabel j) (idleProj.relabel j) tailJoin
    fromChosen fromIdle atTail atChosen atOther oldJoin ih'
  exact law B β Δ (key.relabel j) (oldProj.relabel j) (chosenProj.relabel j) (idleProj.relabel j)
    (allOut.relabel j) (sideOut.relabel j) tailJoin (joined.relabel j)
    orig' kept' oldJoin newJoin' tailCount

/-- Consume the actual projection reports without fabricating a decoded
head or tail. The unselected map input is its genuine filter tail. -/
theorem exact_OpenProjectedCountBranch : ExactOpenProjectedCountBranch := by
  intro side law B α Γ code rawRow tail pool vt vi vc idle allOut chosenOut idleOut joined reports
  have moved : D B Γ (project idleOut vi) :=
    headTransport scratchTargets (suc idleOut) idle vi Fin.elim0 reports.skipped reports.idleProjected
  apply exact_OpenPairedProjectedCons B α Γ code vc rawRow tail vt allOut chosenOut
    (compared allOut joined) reports.inputCell reports.retained reports.projected reports.chosenProjected
  intro β j Δ target oldProj chosenProj keep mainTail chosenTail orig kept
  have actualChosen := renameInto reports.tailChosen j Δ keep
  have actualIdle := renameInto reports.tailIdle j Δ keep
  have other := renameInto moved j Δ keep
  have newJoin := renameInto reports.joinedProjected j Δ keep
  have inherited := renameInto reports.tailLaw j Δ keep
  rw [filterRename] at actualChosen actualIdle
  rw [projectRename] at other
  rw [renameSide] at newJoin
  rw [atRowsRename] at inherited
  rw [comparedRename]
  exact assemble side law (tail.relabel j) (pool.relabel j) (vt.relabel j) (vi.relabel j)
    oldProj chosenProj (idleOut.relabel j) (allOut.relabel j) (chosenOut.relabel j) (joined.relabel j)
    target actualChosen actualIdle mainTail chosenTail other orig kept newJoin inherited

#print axioms exact_OpenProjectedCountBranch

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchProof
