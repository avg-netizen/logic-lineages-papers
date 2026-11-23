module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedOddPackageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalScalarChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankProgramProof
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankEvenOriginalNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankEvenPhysicalChoiceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
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
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralRankGuard (rankEven)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRankProgramProof (exact_OriginalRawNeutralRankProgram)
open NumberedWindowNeutralSpineExchangeRankProof (exact_OriginalKeepsNeutralRank)
open NumberedWindowInternalNeutralRankEvenOriginalNumericProof (exact_OriginalRankEvenAllInputs)
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
original tuple. Reinstall the actual rank-guarded even callback in its own
literal odd body, retaining the original application core and parsed probes. -/
theorem exact_SelectedLiteralRankEvenPhysicalScalar :
    ∃ (rankProg : Program 1) (C : Program 3),
      (∀ n, evaluate rankProg (n ::ᵥ nil) = rawRank n) ∧ ActualSelectedCoverOutput C ∧
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
        let N := rankEven i (addressRank rankProg) R
        CallbacksAt xs s cv tv raw least ∧
        ActualScalarCalibration s i ∧
        chosenA updated = chosenA v ∧ updated.applicationGuard = guard i (applicationCore least) ∧
        TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
        InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
        TupleAt xs s W i (jRaw i) N (dCore i N permutation) updated ∧
        (∀ c, OriginalOddRules i R c ∧ OriginalOddRules i N c) := by
  obtain ⟨rankProg,rankFit⟩ := exact_OriginalRawNeutralRankProgram
  obtain ⟨C,cover,choose⟩ := exact_SelectedLiteralPhysicalScalar
  refine ⟨rankProg,C,rankFit,cover,?_⟩
  intro xs s W valid
  obtain ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps,guardEq,tuple,report,_,_⟩ := choose xs s W valid
  let raw := typedRaw5 root other windowProg V
  let least := packedLeastProgram C X windowProg s
  let i := addressScalar cv tv windowProg least
  let R := addressPositive cv tv raw least
  let N := rankEven i (addressRank rankProg) R
  let updated := frontendInputs i least v
  have calibrated := tuple.1
  have newEven := exact_OriginalRankEvenAllInputs xs s (exact_OriginalKeepsNeutralRank s)
    i rankProg R calibrated.1 rankFit calibrated.2.2.1
  have fresh := exact_ReinstallTypedList xs s i N permutation calibrated.1 newEven exact_OriginalLiteralCountFit
  have newTuple := rebuild xs s W valid.2.1 i (jRaw i) R (dCore i R permutation)
    N (applicationCore least) updated tuple guardEq fresh
  exact ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps,guardEq,tuple,report,newTuple,
    fun c => ⟨exact_OriginalOddRules i R c,exact_OriginalOddRules i N c⟩⟩

#print axioms exact_SelectedLiteralRankEvenPhysicalScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankEvenPhysicalChoiceProof
