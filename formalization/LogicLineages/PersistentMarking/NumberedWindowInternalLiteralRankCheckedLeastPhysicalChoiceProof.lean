module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedOddPackageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets

public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankProgramProof
import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankCheckedLeastPhysicalChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
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
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowGuardedGraphTargets (guard)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_PhysicalLeastInstalledTuple exact_ReinstallCalibratedLeast)
open NumberedWindowInternalLiteralPhysicalScalarReinstallProof (exact_ReinstallLiteralPhysicalScalar)
open NumberedWindowInternalLiteralSelectedOddPackageProof (OriginalOddRules exact_OriginalOddRules)

open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalRankCheckedLeast (checkedLeast)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRankProgramProof (exact_OriginalRawNeutralRankProgram)
open NumberedWindowInternalRankCheckedLeastNumericProof (exact_OriginalRankCheckedLeastNumeric)

/-- Make the scalar, positive, application, typed raw, least, and odd
checkers transparent choices for the same finite original window.
Keep the checked genuine J package in both physical even bodies. -/
theorem exact_SelectedLiteralRankCheckedLeastPhysicalScalar :
    ∃ (rankProg : Program 1) (C : Program 3),
    (∀ n, evaluate rankProg (n ::ᵥ nil) = rawRank n) ∧ ActualSelectedCoverOutput C ∧
    ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
      ∃ (cv tv syntaxProg : Program 1) (X : Program 2) (root other windowProg : Program 3)
          (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root xs s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s X ∧
        let raw := typedRaw5 root other windowProg syntaxProg
        let base := packedLeastProgram C X windowProg s
        let least := checkedLeast rankProg base
        let i := addressScalar cv tv windowProg least
        let updated := frontendInputs i least v
        let R := addressPositive cv tv raw least
        let RR := refined i R
        ActualLeastCalibration s base ∧ ActualLeastCalibration s least ∧
        CallbacksAt xs s cv tv raw least ∧
        ActualScalarCalibration s i ∧
        chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore least) ∧
        TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
        InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
        TupleAt xs s W i (jRaw i) RR (dCore i RR permutation) updated ∧
        (∀ c, OriginalOddRules i R c ∧ OriginalOddRules i RR c) := by
  obtain ⟨rankProg,rankFit⟩ := exact_OriginalRawNeutralRankProgram
  obtain ⟨C,cover,choose⟩ := exact_PhysicalLeastInstalledTuple
  refine ⟨rankProg,C,rankFit,cover,?_⟩
  intro xs s W valid
  obtain ⟨oldI,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,
    hroot,hother,hsyntax,hwindow,hX,baseCal,_,prior,_,_⟩ := choose xs s W valid
  let raw := typedRaw5 root other windowProg syntaxProg
  let base := packedLeastProgram C X windowProg s
  let least := checkedLeast rankProg base
  let i := addressScalar cv tv windowProg least
  let R := addressPositive cv tv raw least
  have checked : ActualLeastCalibration s least :=
    exact_OriginalRankCheckedLeastNumeric s rankProg base rankFit baseCal
  have physical := exact_ReinstallCalibratedLeast xs s W valid oldI j cv tv d oldCore
    raw base least v prior checked
  obtain ⟨isc,keepA,hguard,tuple,report,refinedTuple⟩ :=
    exact_ReinstallLiteralPhysicalScalar xs s W valid oldI j cv tv d oldCore windowProg raw least v
      hwindow physical
  exact ⟨cv,tv,syntaxProg,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    baseCal,checked,physical.2.2.1,isc,keepA,hguard,tuple,report,refinedTuple,
    fun c => ⟨exact_OriginalOddRules i R c,exact_OriginalOddRules i (refined i R) c⟩⟩

#print axioms exact_SelectedLiteralRankCheckedLeastPhysicalScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankCheckedLeastPhysicalChoiceProof
