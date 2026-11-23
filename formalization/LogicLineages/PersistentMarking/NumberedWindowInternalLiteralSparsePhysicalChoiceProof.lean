module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparsePhysicalReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparsePhysicalChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalSparseTuple (InstalledReportAt CallbacksAt)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowGuardedGraphTargets (guard)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_PhysicalLeastInstalledTuple)
open NumberedWindowInternalLiteralSparsePhysicalReinstallProof (reinstallPhysical)

/-- One selected actual packed least and the exact same typed raw window are
physically used in p and the even program. Each literal odd-body tuple is
freshly constructed; the four-field raw report is kept only at unrefined R. -/
theorem selected :
    ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
      ∃ (i cv tv syntaxProg : Program 1) (X : Program 2) (root other windowProg : Program 3)
          (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root xs s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s X ∧
        let raw := typedRaw5 root other windowProg syntaxProg
        let least := packedLeastProgram C X windowProg s
        let updated := frontendInputs i least v
        let R := addressPositive cv tv raw least
        let RR := refined i R
        updated.applicationGuard = guard i (applicationCore least) ∧
        chosenA updated = chosenA v ∧ CallbacksAt xs s cv tv raw least ∧
        TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
        InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
        TupleAt xs s W i (jRaw i) RR (dCore i RR permutation) updated := by
  obtain ⟨C,cover,choose⟩ := exact_PhysicalLeastInstalledTuple
  refine ⟨C,cover,?_⟩
  intro xs s W valid
  obtain ⟨i,j,cv,tv,syntaxProg,X,d,oldCore,oldLeast,root,other,windowProg,v,
    hroot,hother,hsyntax,hwindow,hX,hLeast,_,_,hupdated,hPhysical⟩ := choose xs s W valid
  let raw := typedRaw5 root other windowProg syntaxProg
  let least := packedLeastProgram C X windowProg s
  let updated := frontendInputs i least v
  have dual := reinstallPhysical xs s W valid.2.1 i j cv tv d (applicationCore least)
    raw least updated hPhysical
  exact ⟨i,cv,tv,syntaxProg,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    hPhysical.2.1,hupdated,hPhysical.2.2.1,dual⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparsePhysicalChoiceProof
