module
public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowAddressCheckers

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowRootDispatchAlgorithm (check fixed)

def root (entries : Entries) (s : Settings) := check (fixed entries s.window.2)
def step (entries : Entries) (s : Settings) :=
  NumberedWindowRawContextAlgorithm.windowStep (root entries s) (admitted s)
def positive (entries : Entries) (s : Settings) := NumberedWindowAddressCheckers.positive s (step entries s)
def direct (entries : Entries) (s : Settings) := NumberedWindowAddressCheckers.direct s (step entries s)
end LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers
