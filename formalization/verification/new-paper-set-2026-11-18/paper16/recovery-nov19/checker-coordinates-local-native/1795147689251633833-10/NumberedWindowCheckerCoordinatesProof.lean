module
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinates

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof
open NumberedWindowCheckerCoordinates

theorem exact_ExactCoordinates : ExactCoordinates := by
  constructor
  · intro p c n
    rfl
  · intro p c src dst cert
    rfl
#print axioms exact_ExactCoordinates
end LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof
