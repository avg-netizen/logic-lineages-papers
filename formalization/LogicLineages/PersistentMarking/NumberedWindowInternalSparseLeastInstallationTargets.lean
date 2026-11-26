module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)

/-- Changing least changes the positive checker and the source body.
All callbacks, the actual four-field open report and source rules are rederived. -/
def ExactReinstallCalibratedLeast : Prop :=
  ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j cv tv : Program 1) (d oldCore : Program 3) (raw : Program 5)
      (oldLeast newLeast : Program 3) (v : Inputs),
      InstalledTupleAt entries s W i j cv tv d oldCore raw oldLeast v →
      ActualLeastCalibration s newLeast →
      InstalledTupleAt entries s W i j cv tv d oldCore raw newLeast v

/-- The same packed window program is used inside the typed raw step and
the directed exchange of the least evaluator. The new application core
also contains the same actual least evaluator. -/
def ExactPhysicalLeastInstalledTuple : Prop :=
  ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
      ∃ (i j cv tv syntaxProg : Program 1) (X : Program 2)
        (d oldCore oldLeast root other windowProg : Program 3) (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s X ∧
        let raw := typedRaw5 root other windowProg syntaxProg
        let least := packedLeastProgram C X windowProg s
        let updated := frontendInputs i least v
        ActualLeastCalibration s least ∧
        InstalledTupleAt entries s W i j cv tv d oldCore raw oldLeast v ∧
        InstalledTupleAt entries s W i j cv tv d oldCore raw least v ∧
        chosenA updated = chosenA v ∧
        InstalledTupleAt entries s W i j cv tv d (applicationCore least) raw least updated

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
