import LogicLineages.PersistentMarking.DecisionSourceMarkProof
namespace LogicLineages.PersistentMarking.DecisionSourceFoundationChecks
theorem exact_InitialUniverse : DecisionSourceTargets.InitialUniverse := DecisionSourceBasicProof.initial
#print axioms exact_InitialUniverse
theorem exact_RootType : DecisionSourceTargets.RootType := DecisionSourceBasicProof.rootType
#print axioms exact_RootType
theorem exact_SourceOccurrence : DecisionSourceTargets.SourceOccurrence := DecisionSourceBasicProof.occurrence
#print axioms exact_SourceOccurrence
theorem exact_SourceAt : DecisionSourceTargets.SourceAt := DecisionSourceBasicProof.sourceAt
#print axioms exact_SourceAt
theorem exact_SourceMark : DecisionSourceTargets.SourceMark := DecisionSourceMarkProof.sourceMark
#print axioms exact_SourceMark
theorem exact_SourceRetype : DecisionSourceTargets.SourceRetype := DecisionSourceMarkProof.sourceRetype
#print axioms exact_SourceRetype
theorem exact_UniverseWeakening : DecisionSourceTargets.UniverseWeakening := DecisionSourceBasicProof.weakening
#print axioms exact_UniverseWeakening
end LogicLineages.PersistentMarking.DecisionSourceFoundationChecks
