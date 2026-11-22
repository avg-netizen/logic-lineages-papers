module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachLocalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseRoundReachChecks (exact_SeedRoundZero exact_RoundEdgeExtension)
open NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets

theorem fromActualFirstRounds {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (E : Program 4) (ctx ty vertices a b before after : OTerm α)
    (ma : Nonempty (Derivation body Γ (memberGraph vertices a)))
    (mb : Nonempty (Derivation body Γ (memberGraph vertices b)))
    (edge : Nonempty (Derivation body Γ (acceptEdge E ctx ty a b)))
    (beforeRun : Nonempty (Derivation body Γ (roundGraph E before z vertices ctx ty a)))
    (afterRun : Nonempty (Derivation body Γ (roundGraph E after (suc z) vertices ctx ty a))) :
    FirstRoundReports E body Γ ctx ty vertices a b before after := by
  obtain ⟨zero⟩ := exact_SeedRoundZero E body α Γ before vertices ctx ty a
  obtain ⟨step⟩ := exact_RoundEdgeExtension E body α Γ before after z vertices ctx ty a a b
  obtain ⟨oa⟩ := ma
  obtain ⟨ob⟩ := mb
  obtain ⟨raw⟩ := edge
  obtain ⟨beforeGraph⟩ := beforeRun
  obtain ⟨afterGraph⟩ := afterRun
  have started := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination zero beforeGraph)) oa
  have arrived := Derivation.implicationElimination step
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction beforeGraph afterGraph)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction started raw) ob))
  exact ⟨⟨oa⟩,⟨ob⟩,⟨raw⟩,⟨beforeGraph⟩,⟨afterGraph⟩,⟨started⟩,⟨arrived⟩⟩

#print axioms fromActualFirstRounds
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachLocalProof
