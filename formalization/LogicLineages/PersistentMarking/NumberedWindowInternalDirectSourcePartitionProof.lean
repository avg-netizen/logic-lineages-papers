module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionAppendProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison (permutation)
open ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof (permutationAgreement)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectSourcePartitionRawProof (exact_OpenRawSourceDecode)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough renameParser)
open NumberedWindowInternalDirectSourcePartitionAppendProof (exact_OpenSourcePartitionAppend)
open NumberedWindowInternalDirectSourcePartitionTargets

attribute [local irreducible] programGraph

theorem exact_OpenSourcePartition : ExactOpenSourcePartition := by
  intro B α Γ src kept removed goal accepted next
  apply exact_OpenRawSourceDecode partitionScratch B α Γ src kept removed goal accepted
  intro β j Δ ds dk dr hold parsed core
  apply exact_OpenSourcePartitionAppend permutation ds dk dr (goal.relabel j) core
  intro γ k Θ both keep appended compared
  let g := k ∘ j
  have src' := renameParser (src.relabel j) ds parsed.source k Θ keep
  have kept' := renameParser (kept.relabel j) dk parsed.kept k Θ keep
  have removed' := renameParser (removed.relabel j) dr parsed.removed k Θ keep
  have parsed' : ParsedTriplet B Θ (src.relabel g) (kept.relabel g) (removed.relabel g)
      (ds.relabel k) (dk.relabel k) (dr.relabel k) :=
    ⟨by simpa only [g,Term.relabel_relabel] using src',
     by simpa only [g,Term.relabel_relabel] using kept',
     by simpa only [g,Term.relabel_relabel] using removed'⟩
  have counts := permutationAgreement (ds.relabel k) both compared
  rw [formulaRelabelComposition j k goal]
  exact next γ g Θ (ds.relabel k) (dk.relabel k) (dr.relabel k) both
    (keepThrough j k hold keep) ⟨parsed',appended,counts⟩

#print axioms exact_OpenSourcePartition
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionProof
