import LogicLineages.PersistentMarking.InsertionProof
namespace LogicLineages.PersistentMarking.InsertionChecks

theorem insertedAtDepth : InsertionTargets.InsertedAtDepth := InsertionProof.insertedAtDepth
theorem retainedLocalIndex : InsertionTargets.RetainedLocalIndex := InsertionProof.retainedLocalIndex
theorem boundUnderBinder : InsertionTargets.BoundUnderBinder := InsertionProof.boundUnderBinder
#print axioms insertedAtDepth
#print axioms retainedLocalIndex
#print axioms boundUnderBinder
end LogicLineages.PersistentMarking.InsertionChecks
