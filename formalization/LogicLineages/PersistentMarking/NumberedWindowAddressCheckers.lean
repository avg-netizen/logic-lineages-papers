module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressCheckers
open NumberedWindowScalarAlgorithm

def multisetDomain (s : NumberedWindowScalarAlgorithm.Settings) := NumberedWindowDirectAlgorithm.typedList (NumberedWindowScalarAlgorithm.scalar s)
def positive (s : NumberedWindowScalarAlgorithm.Settings) (step : NumberedWindowPositivePathAlgorithm.Step) :=
  NumberedWindowPositivePathAlgorithm.addressRS step (NumberedWindowScalarAlgorithm.least s)
def direct (s : NumberedWindowScalarAlgorithm.Settings) (step : NumberedWindowPositivePathAlgorithm.Step) :=
  NumberedWindowDirectAlgorithm.direct (NumberedWindowScalarAlgorithm.scalar s) (positive s step)
end LogicLineages.PersistentMarking.NumberedWindowAddressCheckers
