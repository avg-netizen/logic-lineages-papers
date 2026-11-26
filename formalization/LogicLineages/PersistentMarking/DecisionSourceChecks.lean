import LogicLineages.PersistentMarking.DecisionSourceFoundationChecks
import LogicLineages.PersistentMarking.DecisionSourceSubstitutionChecks
import LogicLineages.PersistentMarking.DecisionSourceOwnerObservedChecks
import LogicLineages.PersistentMarking.DecisionSourceCallChecks
namespace LogicLineages.PersistentMarking.DecisionSourceChecks
theorem exact_allSuppliers :
  DecisionSourceTargets.InitialUniverse ∧ DecisionSourceTargets.RootType ∧
  DecisionSourceTargets.SourceOccurrence ∧ DecisionSourceTargets.SourceAt ∧
  DecisionSourceTargets.SourceMark ∧ DecisionSourceTargets.SourceRetype ∧
  DecisionSourceTargets.SourceBoundSubstitution ∧ DecisionSourceTargets.SourceFullCall ∧
  DecisionSourceTargets.SourceOwnerTuple ∧ DecisionSourceTargets.UniverseWeakening ∧
  DecisionSourceTargets.ObservedTypes :=
  ⟨DecisionSourceBasicProof.initial,DecisionSourceBasicProof.rootType,
   DecisionSourceBasicProof.occurrence,DecisionSourceBasicProof.sourceAt,
   DecisionSourceMarkProof.sourceMark,DecisionSourceMarkProof.sourceRetype,
   DecisionSourceSubstitutionProof.boundSubstitution,DecisionSourceCallProof.fullCall,
   DecisionSourceOwnerProof.ownerTuple,DecisionSourceBasicProof.weakening,
   DecisionObservedTypesProof.observedTypes⟩
#print axioms exact_allSuppliers
end LogicLineages.PersistentMarking.DecisionSourceChecks
