module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalStrongInduction (lift)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb zSubst sucSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalCoverOwnEarlierTargets
open NumberedWindowInternalCoverOwnEarlierSyntaxProof (ownAllSubst)

theorem ownAtRelabel {α β : Type} (V : Program 1) (W C : Program 3) (s : Settings)
    (q : OTerm α) (j : α → β) :
    (ownAt V W C s q).relabel j = ownAt V W C s (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (ownAt V W C s q).subst (fun a => emb (.var (j a))) = _
  have exactSubst (ts : α → OTerm β) :
      (ownAt V W C s q).subst (fun a => emb (ts a)) = ownAt V W C s (q.subst ts) := by
    simp only [ownAt,impSubst,unarySubst,ownAllSubst,sucSubst,zSubst]
  rw [exactSubst,← termRelabelAsSubst]

theorem combinedOwnMotiveLift {α : Type} (V : Program 1) (W C : Program 3) (s : Settings) :
    lift (ownMotive (α := α) V W C s) = ownMotive (α := α ⊕ Fin 1) V W C s := by
  unfold lift ownMotive
  rw [ownAtRelabel] <;> rfl

#print axioms ownAtRelabel
#print axioms combinedOwnMotiveLift

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionBindingProof
