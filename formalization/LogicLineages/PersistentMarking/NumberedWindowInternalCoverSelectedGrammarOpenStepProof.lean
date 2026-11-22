module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorSplitProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalCoverSelectedGrammarOpenTargets
open NumberedWindowInternalCoverSelectedGrammarOpenRowProof (exact_OpenSelectedGrammarSuccessorRow)
open NumberedWindowInternalCoverSelectedSuccessorSplitProof (exact_OpenSelectedCoverSuccessorSplit)

theorem exact_OpenSelectedGrammarSuccessorSplit : ExactOpenSelectedGrammarSuccessorSplit := by
  intro body α Γ prev next d H K M ids terms args nextTerms nextArgs old new tRead aRead range tNext aNext
  have row := exact_OpenSelectedGrammarSuccessorRow body α Γ
    prev next d H K M ids terms args old new tRead aRead range
  obtain ⟨components⟩ := exact_OpenSelectedCoverSuccessorSplit body α Γ
    next nextTerms nextArgs H K ids terms args row tNext aNext
  obtain ⟨row⟩ := row
  exact ⟨Derivation.conjunctionIntroduction row components⟩

#print axioms exact_OpenSelectedGrammarSuccessorSplit

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
