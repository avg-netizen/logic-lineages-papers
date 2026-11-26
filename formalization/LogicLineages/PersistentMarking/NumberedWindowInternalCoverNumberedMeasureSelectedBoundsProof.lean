module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedBoundsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureCombine (maximum)
open NumberedWindowInternalCoverNumberedMeasureCombineTargets
open NumberedWindowInternalCoverNumberedMeasureCombineOpenProof (exact_OpenCoverNumberedJoin)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem numberedBoundCases (k ml mr dl dr wl wr p : OTerm α) (Q : Formula α)
    (left : Nonempty (Derivation body Γ (codePair ml dl wl)))
    (right : Nonempty (Derivation body Γ (codePair mr dr wr)))
    (joined : Nonempty (Derivation body Γ (programGraph numberedJoin p ![k,ml,mr])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (width : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      NumberedJoinBounds body Δ (p.relabel j) (k.relabel j) (dl.relabel j) (dr.relabel j)
        (wl.relabel j) (wr.relabel j) width →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  apply programCases maximum ![wl,wr] Q
  intro β j Δ mid keep argMax
  rw [binaryInputsRename] at argMax
  apply programCases maximum ![k.relabel j,mid] (Q.relabel j)
  intro γ g Ξ width retain full
  rw [binaryInputsRename] at full
  have preserved : ∀ f ∈ Γ, f.relabel (g ∘ j) ∈ Ξ := by
    intro f hf
    rw [← formulaRelabelComposition j g f]
    exact retain (f.relabel j) (keep f hf)
  have mlCode := renameInto left (g ∘ j) Ξ preserved
  have mrCode := renameInto right (g ∘ j) Ξ preserved
  have merged := renameInto joined (g ∘ j) Ξ preserved
  have stillArg := renameInto argMax g Ξ retain
  rw [pairRename] at mlCode mrCode
  simp only [programRename,tripleInputsRename] at merged
  simp only [programRename,binaryInputsRename,Term.relabel_relabel] at stillArg
  simp only [Term.relabel_relabel] at full
  have paid := exact_OpenCoverNumberedJoin body γ Ξ (p.relabel (g ∘ j)) (k.relabel (g ∘ j))
    (ml.relabel (g ∘ j)) (mr.relabel (g ∘ j)) (dl.relabel (g ∘ j)) (dr.relabel (g ∘ j))
    (wl.relabel (g ∘ j)) (wr.relabel (g ∘ j)) (mid.relabel g) width mlCode mrCode stillArg full merged
  rw [formulaRelabelComposition j g Q]
  exact next γ (g ∘ j) Ξ width preserved paid

#print axioms numberedBoundCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedBoundsProof
