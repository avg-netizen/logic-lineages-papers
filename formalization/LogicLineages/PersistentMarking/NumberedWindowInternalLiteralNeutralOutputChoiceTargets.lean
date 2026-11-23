module

public import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedOddPackageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralOutputChoiceTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseTuple (CallbacksAt InstalledReportAt)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralSelectedOddPackageProof (OriginalOddRules)


open NumberedWindowInternalApplicationOutputGuardReinstallTargets (selectOutputInputs)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral neutralWithCarrier)
open NumberedWindowInternalAuxBottomMembership (augmented)

/-- The complete original physical neutral selection, plus one tuple
with the genuinely reselected guarded p/h on that same neutral body. -/
def SelectedNeutralOutputAt (C : Program 3) (xs : Entries) (s : Settings) (W : List ProbeTy) : Prop :=
  ∃ (cv tv syntaxProg : Program 1) (X : Program 2) (root other windowProg : Program 3)
      (v : Inputs),
    ActualRoot (NumberedWindowConcreteCheckers.root xs s) root ∧
    ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
    ActualTermExchange s X ∧
    let raw := typedRaw5 root other windowProg syntaxProg
    let least := packedLeastProgram C X windowProg s
    let i := addressScalar cv tv windowProg least
    let updated := frontendInputs i least v
    let chosen := selectOutputInputs i updated
    let R := addressPositive cv tv raw least
    let N := augmented i (neutralWithCarrier i R)
    CallbacksAt xs s cv tv raw least ∧
    ActualScalarCalibration s i ∧
    chosenA updated = chosenA v ∧ updated.applicationGuard = applicationGuard i least ∧
    TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
    InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
    TupleAt xs s W i (jRaw i) N (dCore i N permutation) updated ∧
    literalNeutral i R = data i (jRaw i) N (dCore i N permutation) ∧
    (∀ c, OriginalOddRules i R c ∧ OriginalOddRules i N c) ∧
    chosenA chosen = chosenA v ∧
    chosen.applicationGuard = outputGuard i (refinedApplication (applicationGuard i least)) ∧
    TupleAt xs s W i (jRaw i) N (dCore i N permutation) chosen

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralOutputChoiceTargets
