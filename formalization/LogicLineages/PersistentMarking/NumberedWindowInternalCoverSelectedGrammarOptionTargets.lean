module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalUnpair (left right)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalCoverSelectedGrammarTargets (selectedTerms)

/-- Original factored generator input is [H,K,unshifted measurement].
Give the literal recursive term program its actual [depth,H,K,max] tape. -/
def termListAtMeasure : Program 3 :=
  .composition selectedTerms ![reorder left ![2],.projection 0,.projection 1,reorder right ![2]]

/-- Encode the actual some-list constructor, without changing the list. -/
def selectedGrammarOption : Program 3 :=
  .composition .succ (fun _ : Fin 1 => termListAtMeasure)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
