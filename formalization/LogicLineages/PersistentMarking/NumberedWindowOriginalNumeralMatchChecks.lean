import LogicLineages.PersistentMarking.NumberedWindowOriginalNumeralMatchTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteCheckersChecks
namespace LogicLineages.PersistentMarking.NumberedWindowOriginalNumeralMatchChecks
open NumberedWindowOriginalNumeralMatchTargets
theorem exact_OriginalNumericalMatching : OriginalNumericalMatching := by
  intro S K hk
  rw [(NumberedWindowArithmeticConcreteCheckersChecks.exact_AllFourOriginalCheckers S K).2.2.1]
  intro f g u v w edge app
  obtain ⟨b,z,_,ha,he⟩ := NumberedWindowApplicationMatchChecks.exact_BackwardAddressMatching S K hk f g u v w edge app
  exact ⟨b,z,ha,he⟩
#print axioms exact_OriginalNumericalMatching
end LogicLineages.PersistentMarking.NumberedWindowOriginalNumeralMatchChecks
