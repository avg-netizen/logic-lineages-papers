module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressChecks
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationEdgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationEdgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralInstallationChecks
open NumberedWindowInternalSparseCoverInstallationTargets
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeChecks (exact_GuardedExchangeCalibration)
open NumberedWindowInternalSparseDirectedInstallationChecks (exact_DirectedInstallation)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseInstalledOccurrenceChecks (exact_UnconditionalCoverOccurrence)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_ReinstallCalibratedLeast)
open NumberedWindowInternalSparseApplicationReinstallChecks (exact_ReinstallGuardedApplicationTuple)
open NumberedWindowInternalSparsePackedLeastNumericChecks (exact_PackedLeastComposition)
open NumberedWindowInternalSparseMinimumEdgeChecks (exact_MinimumEdgeBound)
open NumberedWindowInternalSparsePositiveWindowChecks (exact_PhysicalPositiveWindowsFromRetained)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)

open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedWindowInternalSparseSymmetricExchangeTargets (swapExchange pairedExchange)
open NumberedWindowInternalSparseSymmetricInstallationTargets
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowExchangeAlgorithm (bits)

open NumberedWindowInternalSparseCoveredInstallationTargets
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseSymmetricInstallationChecks (exact_PairedCalibration)

open NumberedWindowInternalSparseStructuralApplicationTargets (syntaxWindow window exchange)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoStepChecks (exact_PhysicalAuxMemoExchange)
open NumberedWindowInternalSparseCanonicalAddressTargets (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressChecks (exact_AddressScalarCalibration)
open NumberedWindowInternalSparseScalarInstallationChecks (exact_PhysicalEdgeCarriers exact_ReinstallScalar)
open NumberedWindowInternalSparseStructuralApplicationChecks (exact_SyntaxWindowCalibration exact_StructuralFunctionEdge)
open NumberedWindowInternalSparseStructuralInstallationTargets

theorem exact_InstallAt : ExactInstallAt := by
  intro C V cover validV entries s W valid symmetric covered
  obtain ⟨_,_,tuples⟩ := exact_DirectedInstallation
  obtain ⟨i,j,cv,tv,previousV,base,d,oldCore,oldLeast,root,other,baseW,v,hRoot,hOther,
    _,hBaseW,hBase,_,typedTuple,_⟩ := tuples entries s W valid
  let improvedW := syntaxWindow baseW V
  let memo := selected (step base V)
  let Wp := window C s baseW V
  let X := exchange C s base V
  let raw := typedRaw5 root other Wp V
  let least := packedLeastProgram C X Wp s
  let newI := addressScalar cv tv Wp least
  have startWindow := exact_SyntaxWindowCalibration s baseW V hBaseW validV
  have hw := NumberedWindowInternalSparseCoveredWindowChecks.exact_CoveredWindowCalibration C s improvedW cover covered startWindow
  have hx := exact_PhysicalAuxMemoExchange s base V hBase validV
  have hp := exact_PairedCalibration s memo symmetric hx
  have he := exact_GuardedExchangeCalibration C s (pairedExchange memo) cover hp
  have cal := exact_PackedLeastComposition s C X Wp cover he hw
  have rc := NumberedWindowInternalSparseTypedRawChecks.exact_TypedRaw5Calibration entries s root other Wp V hRoot hOther validV hw
  have newRaw := NumberedWindowInternalSparseTypedRawInstallationChecks.exact_ReinstallCalibratedRawTuple entries s W valid
    i j cv tv d oldCore (typedRaw5 root other baseW previousV) raw oldLeast v typedTuple rc
  have full := exact_ReinstallCalibratedLeast entries s W valid i j cv tv d oldCore raw oldLeast least v newRaw cal
  have scalar := exact_AddressScalarCalibration s cv tv Wp least full.2.2.1.1 full.2.2.1.2.1 hw cal
  obtain ⟨sameA,installed⟩ := exact_ReinstallScalar entries s W valid newI i j cv tv d oldCore raw least v scalar full
  exact ⟨i,j,cv,tv,base,d,oldCore,oldLeast,root,other,baseW,v,hRoot,hOther,hBase,hBaseW,he,hw,cal,scalar,
    newRaw,full,sameA,installed,exact_PhysicalEdgeCarriers C s memo improvedW root other V cv tv j d,
    exact_UnconditionalCoverOccurrence C X Wp s,exact_MinimumEdgeBound exact_RetainedPredecessor C X Wp s,
    exact_PhysicalPositiveWindowsFromRetained exact_RetainedPredecessor C X Wp root other V s,
    NumberedWindowInternalSparseCoverInstallationEdgeProof.edgeCover C s (pairedExchange memo) Wp,
    NumberedWindowInternalSparseAdjacentMinimumChecks.exact_EdgeMinimumOrder C s (pairedExchange memo) Wp,
    NumberedWindowInternalSparseAdjacentMinimumChecks.exact_MutualEdgeMinimumEquality C s (pairedExchange memo) Wp,
    NumberedWindowInternalSparseSymmetricExchangeChecks.exact_PairedEdgeMinimumEquality C s memo Wp,
    NumberedWindowInternalSparseCoveredInstallationChecks.exact_CoveredEdgeValues C s memo improvedW,
    exact_StructuralFunctionEdge C s base baseW V⟩

theorem exact_StructuralInstallation : ExactStructuralInstallation := by
  obtain ⟨C,cover,_⟩ := exact_DirectedInstallation
  obtain ⟨V,syntaxV⟩ := NumberedWindowSyntaxProgramProof.termProgram
  exact ⟨C,V,cover,syntaxV,exact_InstallAt C V cover syntaxV⟩

#print axioms exact_InstallAt
#print axioms exact_StructuralInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralInstallationChecks
