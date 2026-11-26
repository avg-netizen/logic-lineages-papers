module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFunctionalGraphTargets (UniqueResult)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore applicationGuard)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)

/-- Two genuine acceptances at the same arbitrary open inputs force an
ordinary object equality. No numeral calibration or window validity
is presumed, and no result-carrier claim is part of this target. -/
def ExactUniqueGuardedApplication : Prop :=
  ∀ (i : Program 1) (least : Program 3), UniqueResult (applicationGuard i least)

/-- Retain the same physical i/j/cv/tv/d/raw/least and same settings,
window, positive program and source body. Reinstall only actual p₀
and the dependent v.applicationGuard with fresh chosenH/typing/
alignment proofs at that new AST. chosenA is literally unchanged. -/
def ExactReinstallGuardedApplicationTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j cv tv : Program 1) (d oldCore : Program 3) (raw : Program 5)
      (least : Program 3) (v : Inputs),
      InstalledTupleAt xs s W i j cv tv d oldCore raw least v →
      let updated := frontendInputs i least v
      chosenA updated = chosenA v ∧
        InstalledTupleAt xs s W i j cv tv d (applicationCore least) raw least updated

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallTargets
