module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchObservedProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxParentProof (exact_OpenSelectedGrammarAuxParent)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets

theorem exact_OpenSelectedGrammarAuxScratchAtObserved : ExactOpenSelectedGrammarAuxScratchAtObserved := by
  intro V Measure s body α Γ m d maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs
    prev prevTerms prevArgs next vertices nextArgs dom cod fn arg paid before after
  let H := headsTerm s α
  let K := typesTerm s α
  let parent := auxiliaryTerm dom cod fn arg
  obtain ⟨member⟩ := exact_OpenSelectedGrammarAuxParent body α Γ
    d H K maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs
    prev prevTerms prevArgs next vertices nextArgs dom cod fn arg
    paid.functionReport paid.argumentReport paid.functionMember paid.argumentMember
    paid.functionDepth paid.functionWidth paid.argumentDepth paid.argumentWidth
    before after paid.domainMember paid.codomainMember
  have term := exact_ObservedSelectedTerms (suc d) H K maxNumeral next vertices nextArgs after
  obtain ⟨⟨option⟩,⟨scratch⟩⟩ := exact_OpenSelectedGrammarFactoredScratch V Measure s
    m (suc d) maxNumeral vertices parent paid.validity paid.measure paid.measureCode term
  exact ⟨Derivation.conjunctionIntroduction option (Derivation.conjunctionIntroduction scratch member)⟩

#print axioms exact_OpenSelectedGrammarAuxScratchAtObserved

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchObservedProof
