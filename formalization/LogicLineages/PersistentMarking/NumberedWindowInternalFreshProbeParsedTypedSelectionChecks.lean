module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedSelectionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramChecks
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedSelectionChecks
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedTypedSelectionTargets
open NumberedWindowInternalFreshProbeParsedTypedNumericChecks (exact_ParsedTypedCalibration)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks
  (exact_OpenLiteralParsedFresh exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeParsedEmitterNumericChecks (exact_OriginalParsedFreshSelection)
open NumberedWindowConcreteGuardedGraphChecks (exact_ConcreteGuardedApplication)
open NumberedWindowTypedProbeProgramChecks (exact_TypedProbePrograms)
open NumberedWindowAddressApplicationProgramChecks (exact_ApplicationPrograms)
open NumberedWindowInternalPresentationTargets (data)

theorem exact_ConcreteParsedTypedTuple : ExactConcreteParsedTypedTuple := by
  intro xs s W valid
  obtain ⟨i,j,r,d,p,he,hi,hr,hp,hu,hg⟩ := exact_ConcreteGuardedApplication xs s
  obtain ⟨oldTyped,ht⟩ := (exact_TypedProbePrograms s).1
  obtain ⟨optionApp,happ⟩ := (exact_ApplicationPrograms s).1
  obtain ⟨scalarProg,bound,hsource,_⟩ := exact_OriginalParsedFreshSelection s
  let v : Inputs := ⟨oldTyped,optionApp,p,scalarProg,bound⟩
  have cal : CalibratedInputs s v := ⟨hsource,ht,happ,hp⟩
  obtain ⟨ha,hh⟩ := exact_ParsedTypedCalibration s W valid v cal
  exact ⟨i,j,r,d,v,he,hi,hr,cal,hu,hg,ha,hh,
    fun c => exact_SameParsedTypedProbeTotal v W valid.2.1 (data i j r d) c,
    exact_OpenLiteralParsedFresh v W⟩

#print axioms exact_ConcreteParsedTypedTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedSelectionChecks
