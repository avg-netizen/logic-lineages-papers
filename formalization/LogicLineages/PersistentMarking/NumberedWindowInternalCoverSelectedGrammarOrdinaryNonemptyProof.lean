module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryNonemptyTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryNonemptyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalCoverSelectedGrammarNonemptyArgsBoundsProof (exact_OpenSelectedNonemptyArgsAtBounds)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (OrdinaryOwnInputs)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof (exact_OpenSelectedGrammarOrdinaryScratch)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryNonemptyTargets

theorem exact_OpenSelectedGrammarOrdinaryNonemptyScratch : ExactOpenSelectedGrammarOrdinaryNonemptyScratch := by
  intro V Measure W s body α Γ m d M dA MA dq Mq dr Mr qState qTerms qArgs rState rTerms rArgs
    prev prevTerms prevArgs consState consTerms consArgs vertices ctx ty h q r H K a key
    typed ih qScope rScope rHit qd qm rd rm before after outerD outerM head valid measured pair held
  have hit := exact_OpenSelectedNonemptyArgsAtBounds W body α Γ dA H K MA dq Mq dr Mr
    qState qTerms qArgs rState rTerms rArgs prev prevTerms prevArgs consState consTerms consArgs
    ctx ty q r typed ih qScope rScope rHit qd qm rd rm before after
  have paid : OrdinaryOwnInputs V Measure s body Γ m d M (suc dA) MA consState consTerms consArgs h a :=
    { argumentScope := after, argumentHit := hit, argumentDepth := outerD, argumentWidth := outerM
      headHit := head, validity := valid, measurement := measured, parentPair := pair }
  exact exact_OpenSelectedGrammarOrdinaryScratch V Measure s body α Γ
    m d M (suc dA) MA consState consTerms consArgs vertices h a paid held

#print axioms exact_OpenSelectedGrammarOrdinaryNonemptyScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryNonemptyProof
