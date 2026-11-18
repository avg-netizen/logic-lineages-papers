import LogicLineages.PersistentMarking.SubstitutionProof
namespace LogicLineages.PersistentMarking.SubstitutionChecks

theorem shiftZero : SubstitutionTargets.ShiftZero := SubstitutionProof.shiftZero
theorem shiftArgsZero : SubstitutionTargets.ShiftArgsZero := SubstitutionProof.shiftArgsZero
theorem shiftAdd : SubstitutionTargets.ShiftAdd := SubstitutionProof.shiftAdd
theorem shiftArgsAdd : SubstitutionTargets.ShiftArgsAdd := SubstitutionProof.shiftArgsAdd
theorem emptySubstitution : SubstitutionTargets.EmptySubstitution := SubstitutionProof.emptySubstitution
theorem emptyArgsSubstitution : SubstitutionTargets.EmptyArgsSubstitution := SubstitutionProof.emptyArgsSubstitution
theorem shiftType : SubstitutionTargets.ShiftType := SubstitutionProof.shiftType
#print axioms shiftZero
#print axioms shiftArgsZero
#print axioms shiftAdd
#print axioms shiftArgsAdd
#print axioms emptySubstitution
#print axioms emptyArgsSubstitution
#print axioms shiftType
end LogicLineages.PersistentMarking.SubstitutionChecks
