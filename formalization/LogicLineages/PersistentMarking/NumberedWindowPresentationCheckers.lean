module
public import LogicLineages.PersistentMarking.NumberedWindowPresentationClauses
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPresentationCheckers
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressCheckers (multisetDomain)
open NumberedWindowConcreteCheckers (positive direct)
def checks (entries : Entries) (s : Settings) : NumberedWindowPresentationClauses.Checks :=
  ⟨scalar s, multisetDomain s, positive entries s, direct entries s⟩
end LogicLineages.PersistentMarking.NumberedWindowPresentationCheckers
