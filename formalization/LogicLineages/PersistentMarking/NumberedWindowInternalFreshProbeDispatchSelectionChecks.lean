module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchSelectionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphChecks
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchSelectionChecks
open NumberedWindowInternalFreshProbeDispatchSelectionTargets
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchObjectChecks (exact_ProbeTypedTotal)
open NumberedWindowInternalFreshProbeDispatchProgramChecks (exact_ProbeDispatchCalibration)
open NumberedWindowTypedProbeProgramChecks (exact_TypedProbePrograms)
open NumberedWindowAddressApplicationProgramChecks (exact_ApplicationPrograms)
open NumberedWindowConcreteGuardedGraphChecks (exact_ConcreteGuardedApplication)
open NumberedWindowInternalPresentationTargets (data)

/-- Externally ascertain original valuation; internally use the genuine
fixed literal h from that one selected tuple. No extensional change to p
or a is made during either stage. -/
theorem exact_SelectedTypedFromValid : SelectedTypedFromValid := by
  intro s W hw p a hp ha
  obtain ⟨h0,hh0⟩ := (exact_TypedProbePrograms s).1
  obtain ⟨app,happ⟩ := (exact_ApplicationPrograms s).1
  let l : Leaves := ⟨h0,a,app,p⟩
  have hl : calibrated s l := ⟨hh0,ha,happ,hp⟩
  refine ⟨dispatch l W,exact_ProbeDispatchCalibration s W hw l hl,?_⟩
  intro d c
  exact exact_ProbeTypedTotal l W hw.2.1 d c

theorem exact_ConcreteTypedFromValid : ConcreteTypedFromValid := by
  intro xs s W hw
  obtain ⟨i,j,r,d,p,he,hi,hr,hp,hu,hg⟩ := exact_ConcreteGuardedApplication xs s
  obtain ⟨a,ha⟩ := (exact_TypedProbePrograms s).2
  obtain ⟨h,hh,ht⟩ := exact_SelectedTypedFromValid s W hw p a hp ha
  exact ⟨i,j,r,d,p,h,a,he,hi,hr,hp,hu,hg,ha,hh,fun c => ht (data i j r d) c⟩

#print axioms exact_SelectedTypedFromValid
#print axioms exact_ConcreteTypedFromValid
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchSelectionChecks
