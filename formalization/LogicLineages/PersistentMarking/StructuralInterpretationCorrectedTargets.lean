import LogicLineages.PersistentMarking.ProtectedSpineLawTargets
import LogicLineages.PersistentMarking.ProtectedSpineSubstitutionTargets
import LogicLineages.PersistentMarking.ProtectedSpineBoundTargets
import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationTargets
import LogicLineages.PersistentMarking.ProtectedSpineApplicationCounterexampleTargets

namespace LogicLineages.PersistentMarking.StructuralInterpretationCorrected

/-- Paper 16 `lem:structural-interpretation` with the fixed-point
qualification that `paper16/recovery-nov19/MANUSCRIPT-CORRECTION-HANDOFF.md`
asks the manuscript to add at decision.tex 149–155: interpretation and the
original-spine helper are monotone and natural under weakening
(`InterpretationLaws`); interpretation respects capture-avoiding free
substitution and literal simultaneous bound substitution; and AT A FIXED
POINT of the checked operator the helper interprets the full application of
the substituted source, including its undefined cases (`FixedApplication`).
This is a comparator for the corrected statement only. The lemma as printed
today, without the fixed-point qualification, is refuted at the bottom
retained family by `AvailabilityGap`. -/
def CorrectedStructuralInterpretation : Prop :=
  ProtectedSpineLaws.InterpretationLaws ∧
  ProtectedSpineSubstitutionTargets.FreeSubstitution ∧
  ProtectedSpineBoundTargets.BoundSubstitution ∧
  ProtectedSpineFixedApplicationTargets.FixedApplication

/-- The corrected statement together with the checked obstruction to the
unqualified one. -/
def CorrectedWithBoundary : Prop :=
  CorrectedStructuralInterpretation ∧
  ProtectedSpineApplicationCounterexampleTargets.AvailabilityGap

end LogicLineages.PersistentMarking.StructuralInterpretationCorrected
