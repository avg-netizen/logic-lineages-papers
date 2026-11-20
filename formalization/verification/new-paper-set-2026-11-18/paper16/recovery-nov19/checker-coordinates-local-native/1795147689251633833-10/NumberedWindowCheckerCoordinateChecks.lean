module
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinateTargets
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof
import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinateChecks
open NumberedWindowCheckerCoordinateTargets NumberedWindowCheckerCoordinatesProof

theorem exact_FourPresentationPrograms : FourPresentationPrograms := by
  intro xs s
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨pos, hp⟩, ⟨repl, hr⟩⟩ :=
    NumberedWindowConcreteCheckersProgramChecks.exact_AllFourProgramWitnesses xs s
  obtain ⟨dom, edge⟩ := exact_ExactCoordinates
  exact ⟨i, j, pos, repl, fun c n => (dom i c n).trans (hi n),
    fun c n => (dom j c n).trans (hj n),
    fun c a b w => (edge pos c a b w).trans (hp a w b),
    fun c a b w => (edge repl c a b w).trans (hr a w b)⟩

#print axioms NumberedWindowCheckerCoordinatesProof.exact_ExactCoordinates
#print axioms exact_FourPresentationPrograms
end LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinateChecks
