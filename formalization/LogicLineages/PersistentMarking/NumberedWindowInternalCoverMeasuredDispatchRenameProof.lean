module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm measurePair)
open NumberedWindowInternalCoverMeasuredDispatchTargets

variable {body : Positive (Fin 1)} {α β γ : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}
  {Ξ : List (Formula γ)}

theorem keepThrough (j : α → β) (g : β → γ) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (retain : ∀ f ∈ Δ, f.relabel g ∈ Ξ) : ∀ f ∈ Γ, f.relabel (g ∘ j) ∈ Ξ := by
  intro f hf
  rw [← formulaRelabelComposition j g f]
  exact retain (f.relabel j) (keep f hf)

theorem moveParentPair (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (p d w : OTerm α) (source : Nonempty (Derivation body Γ (measurePair p d w))) :
    Nonempty (Derivation body Δ (measurePair (p.relabel j) (d.relabel j) (w.relabel j))) := by
  have h := renameInto source j Δ keep
  change Nonempty (Derivation body Δ ((codePair p (suc d) w).relabel j)) at h
  rw [pairRename,sucRelabel] at h
  exact h

theorem moveWeak (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) (a b : OTerm α)
    (source : Nonempty (Derivation body Γ (ltF a (suc b)))) :
    Nonempty (Derivation body Δ (ltF (a.relabel j) (suc (b.relabel j)))) := by
  have moved := renameInto source j Δ keep
  rw [orderRename,sucRelabel] at moved
  exact moved

theorem moveStoredK (s : Settings) (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (ty : OTerm α) (source : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))) :
    Nonempty (Derivation body Δ (memberGraph (typesTerm s β) (ty.relabel j))) := by
  have h := renameInto source j Δ keep
  simpa only [graphRename,typesTerm,numeralRename] using h

#print axioms keepThrough
#print axioms moveParentPair
#print axioms moveWeak
#print axioms moveStoredK

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
