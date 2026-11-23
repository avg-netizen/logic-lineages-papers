module

public import LogicLineages.NativeModule.PersistentMarking.RankedRestrictionForwardProof
public import LogicLineages.NativeModule.PersistentMarking.RankedRestrictionBackwardProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RankedRestrictionChecks
open Spine RankedRestrictionTargets RankedRestrictionSyntaxProof

theorem exact_ExactRankedRestriction : ExactRankedRestriction := by
  intro S s t hs ht
  have hDomain : ConfinedPair.Domain S s t :=
    ⟨.ground,hs.1,ht.1,(termOrdinary s hs.2).1,(termOrdinary t ht.2).1⟩
  have hSupport := included s t hs.2 ht.2
  constructor
  · constructor
    · intro h
      exact RankedRestrictionForwardProof.strictRPO S s t h.2.1 hs ht
    · intro h
      exact ⟨hDomain,RankedRestrictionBackwardProof.strict S s t h hs ht,hSupport⟩
  · constructor
    · intro h
      exact (RankedRestrictionForwardProof.weak S s t h.2.1).1 hs ht
    · intro h
      refine ⟨hDomain,?_,hSupport⟩
      rcases h with hR | hE
      · exact ElementaryProof.strictIncluded S s t (RankedRestrictionBackwardProof.strict S s t hR hs ht)
      · exact RankedRestrictionEqualityProof.equal S s t hE hs ht

#print axioms exact_ExactRankedRestriction
end LogicLineages.PersistentMarking.RankedRestrictionChecks
