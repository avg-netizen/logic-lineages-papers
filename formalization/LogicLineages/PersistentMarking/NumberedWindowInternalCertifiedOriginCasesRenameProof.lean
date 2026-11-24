module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedOriginCasesRenameProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCertifiedUnionStepProof (SplitCases)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)

theorem exact_OriginalSplitCasesRelabel (S : Data) (c : Nat) (count : Program 2)
    {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}
    (a b v : OTerm α) (goal : Formula α)
    (held : SplitCases S c count Γ a b v goal)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    SplitCases S c count Δ (a.relabel j) (b.relabel j) (v.relabel j) (goal.relabel j) := by
  constructor
  · intro γ k Ω a' wa carry cert join
    rw [formulaRelabelComposition j k goal]
    exact held.leftOnly γ (k ∘ j) Ω a' wa (keepThrough j k keep carry)
      (by simpa only [← Term.relabel_relabel] using cert)
      (by simpa only [← Term.relabel_relabel] using join)
  · intro γ k Ω b' wb carry cert join
    rw [formulaRelabelComposition j k goal]
    exact held.rightOnly γ (k ∘ j) Ω b' wb (keepThrough j k keep carry)
      (by simpa only [← Term.relabel_relabel] using cert)
      (by simpa only [← Term.relabel_relabel] using join)
  · intro γ k Ω a' b' wa wb carry li ri join
    rw [formulaRelabelComposition j k goal]
    exact held.both γ (k ∘ j) Ω a' b' wa wb (keepThrough j k keep carry)
      (by simpa only [← Term.relabel_relabel] using li)
      (by simpa only [← Term.relabel_relabel] using ri)
      (by simpa only [← Term.relabel_relabel] using join)

#print axioms exact_OriginalSplitCasesRelabel
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedOriginCasesRenameProof
