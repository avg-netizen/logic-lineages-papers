module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedOddPackageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralPhysicalChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow ChildClosed)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
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
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowInternalLiteralSelectedOddPackageProof (OriginalOddRules exact_OriginalOddRules)

open NumberedWindowInternalLiteralPhysicalScalarChoiceProof (exact_SelectedLiteralPhysicalScalar)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (neutralWithCarrier literalNeutral)
open NumberedWindowInternalNeutralAuxiliaryLiteralNumericProof (exact_LiteralNeutralEvenNumeric)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalDirectTypedListInstallProof (exact_ReinstallTypedList)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentCarriersProof (carriers)

private theorem rebuild (xs : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i oldJ : Program 1) (oldR oldD R p₀ : Program 3) (v : Inputs)
    (prior : TupleAt xs s W i oldJ oldR oldD v) (hp : v.applicationGuard = guard i p₀)
    (value : Reinstalled xs s i (jRaw i) R permutation) :
    TupleAt xs s W i (jRaw i) R (dCore i R permutation) v := by
  obtain ⟨_,_,_,cal,unique,_,aCal,hCal,_,shape,_⟩ := prior
  obtain ⟨evaluates,interprets,rules⟩ := value
  let d := dCore i R permutation
  have guards : InputGuards i (jRaw i) R d v.applicationGuard := by
    rw [hp]
    exact (exact_GuardRules i (jRaw i) R d p₀).1
  have total (c : Nat) : TypedProbeTotal (data i (jRaw i) R d) v.applicationGuard
      (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W closed (data i (jRaw i) R d) c
  exact ⟨evaluates,interprets,rules,cal,unique,guards,aCal,hCal,total,shape,
    fun c => carriers i (jRaw i) R d v.applicationGuard (chosenH v W) (chosenA v)
      c guards (total c)⟩

/-- The physical scalar and raw positive callback come from one selected
original tuple. Reinstall the actual layered neutral callback in its own
literal odd body, retaining the original application core and parsed probes. -/
theorem exact_SelectedLiteralNeutralPhysicalScalar :
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
        let N := augmented i (neutralWithCarrier i R)
        CallbacksAt xs s cv tv raw least ∧
        ActualScalarCalibration s i ∧
        chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore least) ∧
        TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
        InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
        TupleAt xs s W i (jRaw i) N (dCore i N permutation) updated ∧
        literalNeutral i R = data i (jRaw i) N (dCore i N permutation) ∧
        (∀ c, OriginalOddRules i R c ∧ OriginalOddRules i N c) := by
  obtain ⟨C,cover,choose⟩ := exact_SelectedLiteralPhysicalScalar
  refine ⟨C,cover,?_⟩
  intro xs s W valid
  obtain ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps,guardEq,tuple,report,_,_⟩ := choose xs s W valid
  let raw := typedRaw5 root other windowProg V
  let least := packedLeastProgram C X windowProg s
  let i := addressScalar cv tv windowProg least
  let R := addressPositive cv tv raw least
  let N := augmented i (neutralWithCarrier i R)
  let updated := frontendInputs i least v
  have calibrated := tuple.1
  have newEven := exact_LiteralNeutralEvenNumeric xs s i R calibrated.1 calibrated.2.2.1
  have fresh := exact_ReinstallTypedList xs s i N permutation calibrated.1 newEven exact_OriginalLiteralCountFit
  have newTuple := rebuild xs s W valid.2.1 i (jRaw i) R (dCore i R permutation)
    N (applicationCore least) updated tuple guardEq fresh
  exact ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps,guardEq,tuple,report,newTuple,rfl,
    fun c => ⟨exact_OriginalOddRules i R c,exact_OriginalOddRules i N c⟩⟩

#print axioms exact_SelectedLiteralNeutralPhysicalScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralPhysicalChoiceProof
