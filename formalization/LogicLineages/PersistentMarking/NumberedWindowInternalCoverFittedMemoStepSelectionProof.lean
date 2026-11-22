module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Functionality aligns the selected successor at the given predecessor,
without opening the shape of that predecessor or of the requested goal. -/
private theorem alignStep (A : Program 2) (T : Program 1) (prior ctx result old value : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior))))
    (table : Nonempty (Derivation body Γ (contextTable (strictAuxUpdate A T) old prior ctx)))
    (update : Nonempty (Derivation body Γ (contextStep (strictAuxUpdate A T) value prior old ctx))) :
    Nonempty (Derivation body Γ (contextStep (strictAuxUpdate A T) (suc result) prior old ctx)) := by
  let R := strictAuxUpdate A T
  let F := selectedIntrinsic R
  let key := suc prior
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx result key).mp parent
  have parentRow := (sameContext R (suc result) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc result) ![key,ctx,z] actual parentRow
  exact outputTransport R value (suc result) ![prior,old,ctx,z] agree update

private theorem moveParent (A : Program 2) (T : Program 1) (prior ctx result : OTerm α)
    {β : Type} (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior)))) :
    Nonempty (Derivation body Δ
      (windowGraph (strictAuxWindow A T) (ctx.relabel j) (result.relabel j) (suc (prior.relabel j)))) := by
  have lifted := renameInto parent j Δ keep
  simpa only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel] using lifted

/-- The two object binders work with an arbitrary predecessor term and an
arbitrary object goal. Thus no packed-list or head-formula normalization
occurs during program totality or graph renaming. -/
private theorem withStep (A : Program 2) (T : Program 1) (prior ctx result old : OTerm α)
    (Q : Formula α)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior))))
    (table : Nonempty (Derivation body Γ (contextTable (strictAuxUpdate A T) old prior ctx)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (contextStep (strictAuxUpdate A T) (suc (result.relabel j))
        (prior.relabel j) (old.relabel j) (ctx.relabel j))) →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  let R := strictAuxUpdate A T
  refine programCases R ![prior,old,ctx,z] Q ?_
  intro β j Δ value keep update
  simp only [quadInputsRename,zRelabel] at update
  have liftTable := renameInto table j Δ keep
  simp only [contextTable,programRename,tripleInputsRename,zRelabel] at liftTable
  have liftParent := moveParent A T prior ctx result j Δ keep parent
  exact next β j Δ keep (alignStep A T (prior.relabel j) (ctx.relabel j) (result.relabel j)
    (old.relabel j) value liftParent liftTable update)

theorem exact_OpenSelectedFittedStepCases (A : Program 2) (T : Program 1) (prior ctx result : OTerm α)
    (Q : Formula α)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (contextStep (strictAuxUpdate A T) (suc (result.relabel j))
        (prior.relabel j) old (ctx.relabel j))) →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  let R := strictAuxUpdate A T
  refine programCases (scratchTable (constantZero 2) R) ![prior,ctx,z] Q ?_
  intro β j Δ old keep table
  simp only [tripleInputsRename,zRelabel] at table
  have liftParent := moveParent A T prior ctx result j Δ keep parent
  refine withStep A T (prior.relabel j) (ctx.relabel j) (result.relabel j) old (Q.relabel j) liftParent table ?_
  intro γ k Ξ retain step
  have preserved : ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ξ := by
    intro f hf
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at step
  rw [formulaRelabelComposition j k Q]
  exact next γ (k ∘ j) Ξ (old.relabel k) preserved step

#print axioms exact_OpenSelectedFittedStepCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
