module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorSplitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorAppendProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorInclusionProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorSplitProof (exact_OpenSelectedCoverSuccessorSplit)
open NumberedWindowInternalCoverSelectedSuccessorAppendProof
  (exact_OpenSelectedCoverTermPartInclusion exact_OpenSelectedCoverArgumentPartInclusion)

theorem exact_OpenSelectedCoverSuccessorInclusion : ExactOpenSelectedCoverSuccessorInclusion := by
  intro body α Γ old next oldTerms nextTerms oldArgs nextArgs H K ids ids' ts ts' args args'
    prior later readOldTerms readNextTerms readOldArgs readNextArgs iIncl tIncl aIncl
  obtain ⟨first⟩ := exact_OpenSelectedCoverSuccessorSplit body α Γ old oldTerms oldArgs H K ids ts args
    prior readOldTerms readOldArgs
  obtain ⟨second⟩ := exact_OpenSelectedCoverSuccessorSplit body α Γ next nextTerms nextArgs H K ids' ts' args'
    later readNextTerms readNextArgs
  obtain ⟨t⟩ := exact_OpenSelectedCoverTermPartInclusion body α Γ oldTerms nextTerms H K ids ids'
    ts ts' args args' ⟨Derivation.conjunctionLeft first⟩ ⟨Derivation.conjunctionLeft second⟩ iIncl tIncl aIncl
  obtain ⟨a⟩ := exact_OpenSelectedCoverArgumentPartInclusion body α Γ oldArgs nextArgs H K ids ids'
    ts ts' args args' ⟨Derivation.conjunctionRight first⟩ ⟨Derivation.conjunctionRight second⟩ iIncl tIncl aIncl
  exact ⟨Derivation.conjunctionIntroduction t a⟩

#print axioms exact_OpenSelectedCoverSuccessorInclusion

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorInclusionProof
