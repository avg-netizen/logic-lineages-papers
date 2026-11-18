import LogicLineages.PersistentMarking.TypedMarkingProof

namespace LogicLineages.PersistentMarking.TypedMarkingChecks

theorem annotationExact : TypedMarkingTargets.AnnotationExact :=
  TypedMarkingProof.annotationExact
theorem partialPreserves : TypedMarkingTargets.PartialPreserves :=
  TypedMarkingProof.partialPreserves
theorem totalPreserves : TypedMarkingTargets.TotalPreserves :=
  TypedMarkingProof.totalPreserves

#print axioms annotationExact
#print axioms partialPreserves
#print axioms totalPreserves
end LogicLineages.PersistentMarking.TypedMarkingChecks
