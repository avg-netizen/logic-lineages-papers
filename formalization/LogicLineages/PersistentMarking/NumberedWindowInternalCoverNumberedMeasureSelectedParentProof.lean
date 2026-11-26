module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedParentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (moveReport)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (selectedArgsMeasure)
open NumberedWindowInternalCoverNumberedMeasureSelectedCutProof (exact_OpenCoverNumberedMeasureCut)
open NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof
  (actualArgsPairCases exact_OpenNumberedJoinFromFields)
open NumberedWindowInternalCoverNumberedMeasureSelectedBoundsProof (numberedBoundCases)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β γ : Type} {Γ : List (Formula α)}
  {Δ : List (Formula β)} {Ξ : List (Formula γ)}

private theorem bothRetained (j : α → β) (k : β → γ)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) (retain : ∀ f ∈ Δ, f.relabel k ∈ Ξ) :
    ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ξ := by
  intro f hf
  rw [← formulaRelabelComposition j k f]
  exact retain (f.relabel j) (keep f hf)

theorem exact_OpenCoverNumberedMeasuredArgs : ExactOpenCoverNumberedMeasuredArgs := by
  intro M A body α Γ h ty k l r p Q parent next
  have cut := exact_OpenCoverNumberedMeasureCut M A body α Γ h ty k l r p parent
  apply actualArgsPairCases A l Q
  intro β j Δ ml dl wl keep left pleft
  apply actualArgsPairCases A (r.relabel j) (Q.relabel j)
  intro γ g Ξ mr dr wr retain right pright
  have paired := bothRetained j g keep retain
  let q := g ∘ j
  have stillCut := moveReport q Ξ paired (numberedMeasureApply A) p (numberedTerm h ty k l r) cut
  rw [numberedRename] at stillCut
  have leftReport := moveReport g Ξ retain (selectedArgsMeasure A) ml (l.relabel j) left
  have prefixPair := renameInto pleft g Ξ retain
  rw [pairRename] at prefixPair
  simp only [Term.relabel_relabel] at leftReport right
  have join := exact_OpenNumberedJoinFromFields A (h.relabel q) (ty.relabel q) (k.relabel q)
    (l.relabel q) (r.relabel q) (p.relabel q) (ml.relabel g) mr stillCut leftReport right
  rw [formulaRelabelComposition j g Q]
  apply numberedBoundCases (k.relabel q) (ml.relabel g) mr (dl.relabel g) dr (wl.relabel g) wr
    (p.relabel q) (Q.relabel q) prefixPair pright join
  intro ζ e Ω width remain due
  let i := e ∘ q
  have preserved := bothRetained q e paired remain
  have one := moveReport e Ω remain (selectedArgsMeasure A) (ml.relabel g) (l.relabel q) leftReport
  have two := moveReport e Ω remain (selectedArgsMeasure A) mr (r.relabel q) right
  have carriedL := renameInto prefixPair e Ω remain
  have carriedR := renameInto pright e Ω remain
  rw [pairRename] at carriedL carriedR
  have data : NumberedMeasuredArgs A body Ω (k.relabel i) (l.relabel i) (r.relabel i) (p.relabel i)
      ((ml.relabel g).relabel e) (mr.relabel e) ((dl.relabel g).relabel e) (dr.relabel e)
      ((wl.relabel g).relabel e) (wr.relabel e) width := by
    refine ⟨?_,?_,carriedL,carriedR,?_⟩
    · dsimp only [i]
      rw [← Term.relabel_relabel]
      exact one
    · dsimp only [i]
      rw [← Term.relabel_relabel]
      exact two
    · simpa only [i,Term.relabel_relabel] using due
  rw [formulaRelabelComposition q e Q]
  exact next ζ i Ω ((ml.relabel g).relabel e) (mr.relabel e) ((dl.relabel g).relabel e) (dr.relabel e)
    ((wl.relabel g).relabel e) (wr.relabel e) width preserved data

#print axioms exact_OpenCoverNumberedMeasuredArgs

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedParentProof
