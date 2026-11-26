module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationWindowProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationSubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRealizationChecks
open NumberedWindowTupleTargets

theorem exact_RealizationInWindow : RealizationInWindow :=
  NumberedWindowRealizationWindowProof.inWindow

theorem exact_RealizationWeakens : RealizationWeakens := by
  intro n m q Q hle h
  exact NumberedWindowRealizationShapeProof.weakensTerm hle h

theorem exact_RealizationShift : RealizationShift := by
  intro n amount cutoff q Q h
  exact NumberedWindowRealizationShapeProof.shiftTerm h amount cutoff

theorem exact_RealizationSubstitution : RealizationSubstitution := by
  intro n depth q Q values Values h hV
  exact NumberedWindowRealizationSubstitutionProof.term hV h depth

#print axioms exact_RealizationInWindow
#print axioms exact_RealizationWeakens
#print axioms exact_RealizationShift
#print axioms exact_RealizationSubstitution

end LogicLineages.PersistentMarking.NumberedWindowRealizationChecks
