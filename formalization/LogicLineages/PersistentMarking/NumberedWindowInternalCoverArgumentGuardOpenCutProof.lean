module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenAlignmentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenCutProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt readRow)
open NumberedWindowInternalCoverSharedMemoTargets (ObservedStep)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverArgumentGuardOpenAlignmentProof (actualArgumentGuardAlignment)
open NumberedWindowInternalCoverArgumentGuardTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

structure AtSuccessor (G : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (prior h a : OTerm α) : Prop where
  packed : Nonempty (Derivation body Γ (eqn (suc prior) (rawCons h a)))
  earlier : Nonempty (Derivation body Γ (ltF a (suc prior)))
  head : Nonempty (Derivation body Γ (unary G (suc z) h))
  tail : Nonempty (Derivation body Γ (unary (argumentReject G) z a))

private theorem readTail (G : Program 1) (prior old h a : OTerm α) (Q : Formula α)
    (step : ObservedStep (argumentRejectUpdate G) body Γ prior old z)
    (hd : Nonempty (Derivation body Γ (unary cellHead h (suc prior))))
    (tl : Nonempty (Derivation body Γ (unary cellTail a (suc prior))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      AtSuccessor G body Δ (prior.relabel j) (h.relabel j) (a.relabel j) →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  let R := argumentRejectUpdate G
  apply programCases (scratchRow (constantZero 2) R) ![a,z,z] Q
  intro β j Δ v keep row
  simp only [tripleInputsRename,zRelabel] at row
  have update := renameInto step.update j Δ keep
  have table := renameInto step.table j Δ keep
  have head' := renameInto hd j Δ keep
  have tail' := renameInto tl j Δ keep
  simp only [programRename,quadInputsRename,zRelabel] at update
  simp only [tableAt,programRename,tripleInputsRename,zRelabel] at table
  simp only [unary,programRename,inputsRename,sucRelabel] at head' tail'
  obtain ⟨packed,earlier,vh,vt⟩ := actualArgumentGuardAlignment G (prior.relabel j)
    (old.relabel j) (h.relabel j) (a.relabel j) v update table head' tail' row
  exact next β j Δ keep ⟨packed,earlier,vh,vt⟩

private theorem withSelectors (G : Program 1) (prior old : OTerm α) (Q : Formula α)
    (step : ObservedStep (argumentRejectUpdate G) body Γ prior old z)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (h a : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      AtSuccessor G body Δ (prior.relabel j) h a →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  apply programCases cellHead ![suc prior] Q
  intro β j Δ h keep head
  apply programCases cellTail ![suc (prior.relabel j)] (Q.relabel j)
  intro γ g Ξ a retain tail
  let k := g ∘ j
  have both := keepThrough j g keep retain
  have hd := renameInto head g Ξ retain
  simp only [programRename,inputsRename,sucRelabel,Term.relabel_relabel] at hd
  simp only [inputsRename,sucRelabel,Term.relabel_relabel] at tail
  have update := renameInto step.update k Ξ both
  have table := renameInto step.table k Ξ both
  simp only [programRename,quadInputsRename,zRelabel] at update
  simp only [tableAt,programRename,tripleInputsRename,zRelabel] at table
  rw [formulaRelabelComposition j g Q]
  apply readTail G (prior.relabel k) (old.relabel k) (h.relabel g) a (Q.relabel k) ⟨table,update⟩ hd tail
  intro δ l Ω carried vals
  simp only [Term.relabel_relabel] at vals
  rw [formulaRelabelComposition k l Q]
  exact next δ (l ∘ k) Ω ((h.relabel g).relabel l) (a.relabel l) (keepThrough k l both carried) vals

theorem actualArgumentGuardSuccessor (G : Program 1) (prior : OTerm α) (Q : Formula α)
    (actual : Nonempty (Derivation body Γ (unary (argumentReject G) z (suc prior))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (h a : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      AtSuccessor G body Δ (prior.relabel j) h a →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  apply exact_OpenCoverSharedMemoRowCases (argumentRejectUpdate G) body α Γ prior z Q actual
  intro β j Δ old keep row
  simp only [zRelabel] at row
  apply withSelectors G (prior.relabel j) old (Q.relabel j) row
  intro γ g Ξ h a retain vals
  simp only [Term.relabel_relabel] at vals
  rw [formulaRelabelComposition j g Q]
  exact next γ (g ∘ j) Ξ h a (keepThrough j g keep retain) vals

#print axioms actualArgumentGuardSuccessor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenCutProof
