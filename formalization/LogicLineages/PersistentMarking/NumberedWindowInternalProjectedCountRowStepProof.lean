module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountRowStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalComplementaryProjectedRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountRowStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalListCodecSupportProof (consGraphRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalOriginRowsFilterTargets (rowCell)
open NumberedWindowInternalOriginScanInductionSyntaxProof (filterRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountBranchTargets (SelectedBranch SideCountCongruence)
open NumberedWindowInternalProjectedCountBranchProof (exact_OpenProjectedCountBranch)
open NumberedWindowInternalComplementaryProjectedRowProof (exact_OpenComplementaryProjectedRow)
open NumberedWindowInternalProjectedCountInductionTargets (compared)
open NumberedWindowInternalProjectedCountInductionSyntaxProof
  (atRowsRename comparedRename projectRename appendedRename)
open NumberedWindowInternalProjectedCountRowStepTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem singletonRename {β : Type} (p : OTerm α) (j : α → β) :
    (fun i : Fin 1 => ((![p] : Fin 1 → OTerm α) i).relabel j) = ![p.relabel j] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

private theorem relocate {β : Type} {Δ : List (Formula β)}
    {co row t pool tl tr l r a al ar u : OTerm α}
    (h : RowStepReports B Γ co row t pool tl tr l r a al ar u)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    RowStepReports B Δ (co.relabel j) (row.relabel j) (t.relabel j) (pool.relabel j)
      (tl.relabel j) (tr.relabel j) (l.relabel j) (r.relabel j)
      (a.relabel j) (al.relabel j) (ar.relabel j) (u.relabel j) := by
  let mv := fun {f} (p : D B Γ f) => renameInto p j Δ keep
  exact ⟨by simpa only [consGraphRename] using mv h.input,
    by simpa only [filterRename] using mv h.priorL,
    by simpa only [filterRename] using mv h.priorR,
    by simpa only [programRename,tripleInputsRename] using mv h.stepL,
    by simpa only [programRename,tripleInputsRename] using mv h.stepR,
    by simpa only [projectRename] using mv h.projected,
    by simpa only [projectRename] using mv h.projectL,
    by simpa only [projectRename] using mv h.projectR,
    by simpa only [appendedRename] using mv h.joinedProjected,
    by simpa only [atRowsRename] using mv h.tailLaw⟩

private theorem selectAt (leftLaw : SideCountCongruence true) (rightLaw : SideCountCongruence false)
    (co row t pool tl tr l r a al ar u key : OTerm α)
    (h : RowStepReports B Γ co row t pool tl tr l r a al ar u)
    (field1 : D B Γ (unary (field 1) key row)) :
    D B Γ (compared a u) := by
  let L := rowCell l row tl ⊓ eqn r tr
  let R := eqn l tl ⊓ rowCell r row tr
  let p := compared a u
  obtain ⟨choices⟩ := exact_OpenComplementaryProjectedRow B α Γ row pool key tl tr l r
    field1 h.stepL h.stepR
  have leftCase : D B Γ (L.imp p) := by
    have shape : Derivation B (L :: Γ) L := Derivation.hypothesis List.mem_cons_self
    have data : SelectedBranch B (L :: Γ) true co row t pool tl tr l r a al ar u :=
      ⟨withHyp h.input L, ⟨Derivation.conjunctionLeft shape⟩, ⟨Derivation.conjunctionRight shape⟩,
        withHyp h.priorL L, withHyp h.priorR L, withHyp h.projected L, withHyp h.projectL L,
        withHyp h.projectR L, withHyp h.joinedProjected L, withHyp h.tailLaw L⟩
    obtain ⟨result⟩ := exact_OpenProjectedCountBranch true leftLaw B α (L :: Γ)
      co row t pool tl tr l r a al ar u data
    exact ⟨Derivation.implicationIntroduction result⟩
  have rightCase : D B Γ (R.imp p) := by
    have shape : Derivation B (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
    have data : SelectedBranch B (R :: Γ) false co row t pool tr tl r l a ar al u :=
      ⟨withHyp h.input R, ⟨Derivation.conjunctionRight shape⟩, ⟨Derivation.conjunctionLeft shape⟩,
        withHyp h.priorR R, withHyp h.priorL R, withHyp h.projected R, withHyp h.projectR R,
        withHyp h.projectL R, withHyp h.joinedProjected R, withHyp h.tailLaw R⟩
    obtain ⟨result⟩ := exact_OpenProjectedCountBranch false rightLaw B α (R :: Γ)
      co row t pool tr tl r l a ar al u data
    exact ⟨Derivation.implicationIntroduction result⟩
  obtain ⟨goL⟩ := leftCase
  obtain ⟨goR⟩ := rightCase
  exact ⟨disjunctionElimination choices goL goR⟩

theorem exact_OpenProjectedCountRowStep : ExactOpenProjectedCountRowStep := by
  intro leftLaw rightLaw B α Γ co row t pool tl tr l r a al ar u support
  apply programCases (field 1) ![row] (compared a u)
  intro β j Δ key keep field1
  rw [singletonRename] at field1
  rw [comparedRename]
  exact selectAt leftLaw rightLaw (co.relabel j) (row.relabel j) (t.relabel j) (pool.relabel j)
    (tl.relabel j) (tr.relabel j) (l.relabel j) (r.relabel j)
    (a.relabel j) (al.relabel j) (ar.relabel j) (u.relabel j) key
    (relocate support j keep) field1

#print axioms exact_OpenProjectedCountRowStep

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountRowStepProof
