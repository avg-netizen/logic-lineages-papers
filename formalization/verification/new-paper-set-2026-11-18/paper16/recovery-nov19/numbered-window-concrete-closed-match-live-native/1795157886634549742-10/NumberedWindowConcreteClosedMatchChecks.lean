module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteClosedMatchTargets
import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowClosedMatchChecks
public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteClosedMatchChecks
open NumberedWindowConcreteClosedMatchTargets

theorem exact_ConcreteClosedMatching : ConcreteClosedMatching := by
  intro xs s matching
  obtain ⟨i,j,r,d,p,he,hi,hr,hp,hu,hg⟩ :=
    NumberedWindowConcreteGuardedGraphChecks.exact_ConcreteGuardedApplication xs s
  refine ⟨i,j,r,d,p,he,hi,hr,hp,hu,hg,?_⟩
  intro c
  exact NumberedWindowClosedMatchChecks.exact_ClosedDerivations _ _ r p he.2.2.1 hp matching _

#print axioms exact_ConcreteClosedMatching
end LogicLineages.PersistentMarking.NumberedWindowConcreteClosedMatchChecks
