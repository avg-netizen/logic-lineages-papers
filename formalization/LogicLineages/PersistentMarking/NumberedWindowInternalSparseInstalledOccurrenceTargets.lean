module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
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

def OpenCoverAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed k : OTerm α),
    Nonempty (Derivation body Γ ((leastGraph C X W s ctx ty seed k).imp (occursInCover C s seed k)))

def ExactUnconditionalCoverOccurrence : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings), OpenCoverAt C X W s

/-- The same chosen exchange and window programs are used at all open inputs,
including by the least program installed in the final application tuple. -/
def ExactInstalledCoverOccurrence : Prop :=
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
        InstalledTupleAt entries s W i j cv tv d (applicationCore least) raw least updated ∧
        OpenCoverAt C X windowProg s

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceTargets
