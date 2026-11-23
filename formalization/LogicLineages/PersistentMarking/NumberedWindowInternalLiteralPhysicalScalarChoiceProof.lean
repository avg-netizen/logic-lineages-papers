module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedOddPackageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
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
open NumberedWindowInternalSparseLeastInstallationChecks (exact_PhysicalLeastInstalledTuple)
open NumberedWindowInternalLiteralPhysicalScalarReinstallProof (exact_ReinstallLiteralPhysicalScalar)
open NumberedWindowInternalLiteralSelectedOddPackageProof (OriginalOddRules exact_OriginalOddRules)

/-- Make the scalar, positive, application, typed raw, least, and odd
checkers transparent choices for the same finite original window.
Keep the checked genuine J package in both physical even bodies. -/
theorem exact_SelectedLiteralPhysicalScalar :
    ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
      ∃ (cv tv syntaxProg : Program 1) (X : Program 2) (root other windowProg : Program 3)
          (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root xs s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s X ∧
        let raw := typedRaw5 root other windowProg syntaxProg
        let least := packedLeastProgram C X windowProg s
        let i := addressScalar cv tv windowProg least
        let updated := frontendInputs i least v
        let R := addressPositive cv tv raw least
        let RR := refined i R
        CallbacksAt xs s cv tv raw least ∧
        ActualScalarCalibration s i ∧
        chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore least) ∧
        TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
        InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
        TupleAt xs s W i (jRaw i) RR (dCore i RR permutation) updated ∧
        (∀ c, OriginalOddRules i R c ∧ OriginalOddRules i RR c) := by
  obtain ⟨C,cover,choose⟩ := exact_PhysicalLeastInstalledTuple
  refine ⟨C,cover,?_⟩
  intro xs s W valid
  obtain ⟨oldI,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,
    hroot,hother,hsyntax,hwindow,hX,hLeast,_,_,_hupdated,hPhysical⟩ := choose xs s W valid
  let raw := typedRaw5 root other windowProg syntaxProg
  let least := packedLeastProgram C X windowProg s
  let i := addressScalar cv tv windowProg least
  let R := addressPositive cv tv raw least
  let update := frontendInputs oldI least v
  obtain ⟨isc,keepA,guardEq,tuple,report,tupleR⟩ :=
    exact_ReinstallLiteralPhysicalScalar xs s W valid oldI j cv tv d (applicationCore least) windowProg
      raw least update hwindow hPhysical
  have can (c : Nat) : OriginalOddRules i R c ∧ OriginalOddRules i (refined i R) c :=
    ⟨exact_OriginalOddRules i R c,exact_OriginalOddRules i (refined i R) c⟩
  have keeps : chosenA (frontendInputs i least update) = chosenA v := keepA.trans _hupdated
  have sameUpdate : frontendInputs i least update = frontendInputs i least v := rfl
  rw [sameUpdate] at keeps guardEq tuple tupleR
  exact ⟨cv,tv,syntaxProg,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    hPhysical.2.2.1,isc,keeps,guardEq,tuple,report,tupleR,can⟩

#print axioms exact_SelectedLiteralPhysicalScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarChoiceProof
