module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTypedProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparseTuplePresentationProof (PresentationAt)
open NumberedWindowInternalSparseTupleApplicationProof (select)
open NumberedWindowGuardedGraphTargets (guard)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowTypedProbeProgramChecks (exact_TypedProbePrograms)
open NumberedWindowInternalFreshProbeParsedEmitterNumericChecks (exact_OriginalParsedFreshSelection)
open NumberedWindowInternalFreshProbeParsedTypedNumericChecks (exact_ParsedTypedCalibration)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks
  (exact_SameParsedTypedProbeTotal exact_OpenLiteralParsedFresh)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)

theorem selectTyped (xs : Entries) (s : Settings) (W : List ProbeTy) (valid : ValidWindow s W)
    (i j : Program 1) (r d : Program 3) (presentation : PresentationAt xs s i j r d) :
    ∃ (p₀ : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v ∧ v.applicationGuard = guard i p₀ := by
  obtain ⟨values,interprets,rules⟩ := presentation
  obtain ⟨optionApp,p₀,happ,hp,unique,guards⟩ := select xs s i j r d values
  obtain ⟨priorTyped,ht⟩ := (exact_TypedProbePrograms s).1
  obtain ⟨scalarProg,bound,hsource,_⟩ := exact_OriginalParsedFreshSelection s
  let v : Inputs := ⟨priorTyped,optionApp,guard i p₀,scalarProg,bound⟩
  let S := data i j r d
  have calibrated : CalibratedInputs s v := ⟨hsource,ht,happ,hp⟩
  obtain ⟨ha,hh⟩ := exact_ParsedTypedCalibration s W valid v calibrated
  have total (c : Nat) : TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W valid.2.1 S c
  have tuple : TupleAt xs s W i j r d v :=
    ⟨values,interprets,rules,calibrated,unique,guards,ha,hh,total,exact_OpenLiteralParsedFresh v W,
      fun c => exact_GivenFreshAlignmentAndCarriers i j r d v.applicationGuard (chosenH v W)
        (chosenA v) c guards (total c)⟩
  exact ⟨p₀,v,tuple,rfl⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTypedProof
