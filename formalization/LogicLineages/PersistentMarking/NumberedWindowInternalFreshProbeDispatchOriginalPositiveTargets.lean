import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowTypedProbeTargets

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalPositiveTargets

/-- Same typing address equivalence for every raw input, including
the originally rejected ones, with no additional supplied typed code. -/
abbrev ExactOriginalTypedAddress : Prop := NumberedWindowTypedProbeTargets.ExactTypedAddress

/-- Same fixed-setting fresh name, actual same-context free carrier and
raw original application and typed output. This retains external
ComputableClass in FreeAt, not an object-language derivation. -/
abbrev ExactOriginalFreshApplication : Prop := NumberedWindowTypedProbeTargets.FreshProbeApplication

/-- The original #613 all-admitted-numerals target verbatim. -/
abbrev ExactOriginalNumericalTotal : Prop := NumberedWindowOriginalProbeTotalTargets.OriginalProbeTotal

/-- The full fixed original numerical window: alias of the same previously
resource-stopped target, not weaker than subtype and typing support plus
full original #613. The mixed Program/original source gate is separate. -/
abbrev ExactOriginalValidWindow : Prop :=
  NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets.ExactOriginalValidWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalPositiveTargets
