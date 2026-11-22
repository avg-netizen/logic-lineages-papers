module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoConsDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt readRow)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalCoverSharedMemoTargets (ObservedStep)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverArgumentMemoConsDataProof (actualArgumentCombine)
open NumberedWindowInternalCoverArgumentMemoTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (x y : OTerm α) (j : α → β) :
    (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
  simp only [pairTerm,addRelabel,mulRelabel]

private theorem carryRow {β : Type} (R : Program 4) (h a before out : OTerm α)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (step : ObservedStep R body Γ (pairTerm h a) before out) :
    ObservedStep R body Δ (pairTerm (h.relabel j) (a.relabel j)) (before.relabel j) (out.relabel j) := by
  have table := renameInto step.table j Δ keep
  have update := renameInto step.update j Δ keep
  simp only [tableAt,programRename,tripleInputsRename,priorRename,zRelabel] at table
  simp only [programRename,quadInputsRename,priorRename,zRelabel] at update
  exact ⟨table,update⟩

private theorem rowCases (F : Program 1) (h a before out : OTerm α) (goal : Formula α)
    (step : ObservedStep (argumentUpdate F) body Γ (pairTerm h a) before out)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (mh mt : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary F mh (h.relabel j))) →
      Nonempty (Derivation body Δ (unary (argumentMeasure F) mt (a.relabel j))) →
      Nonempty (Derivation body Δ (programGraph chosenCombine (out.relabel j) ![mh,mt])) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let R := argumentUpdate F
  apply programCases F ![h] goal
  intro β j Δ mh keep head
  rw [inputsRename] at head
  apply programCases (scratchRow (constantZero 2) R) ![a.relabel j,z,z] (goal.relabel j)
  intro γ g Ξ mt retain tail
  simp only [tripleInputsRename,zRelabel] at tail
  let k := g ∘ j
  have both := keepThrough j g keep retain
  have head' := renameInto head g Ξ retain
  simp only [unaryRename,Term.relabel_relabel] at head'
  have row := carryRow R h a before out k Ξ both step
  have tl : Nonempty (Derivation body Ξ (readRow R mt (a.relabel k))) := tail
  have combined := actualArgumentCombine F (h.relabel k) (a.relabel k) (before.relabel k)
    (out.relabel k) (mh.relabel g) mt row.table row.update head' tl
  rw [formulaRelabelComposition j g goal]
  exact next γ k Ξ (mh.relabel g) mt both head' ((projection R mt (a.relabel k)).mpr tl) combined

theorem exact_OpenCoverArgumentMemoCons : ExactOpenCoverArgumentMemoCons := by
  intro F body α Γ head tail out goal actual next
  let R := argumentUpdate F
  let prior := pairTerm head tail
  apply exact_OpenCoverSharedMemoRowCases R body α Γ prior out goal actual
  intro β j Δ old keep row
  let Fit : OTerm β → Prop := fun before => ObservedStep R body Δ before old (out.relabel j)
  have physical : Fit (pairTerm (head.relabel j) (tail.relabel j)) :=
    Eq.mp (congrArg Fit (priorRename head tail j)) row
  apply rowCases F (head.relabel j) (tail.relabel j) old (out.relabel j) (goal.relabel j) physical
  intro γ g Ξ mh mt retain headReport tailReport combined
  simp only [Term.relabel_relabel] at headReport tailReport combined
  rw [formulaRelabelComposition j g goal]
  exact next γ (g ∘ j) Ξ mh mt (keepThrough j g keep retain) headReport tailReport combined

#print axioms exact_OpenCoverArgumentMemoCons

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoConsProof
