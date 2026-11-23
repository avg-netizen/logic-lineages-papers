module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCompleteRankEvenPhysicalChoiceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRankedTupleProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCompleteOriginalRankedChoiceProof
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

open NumberedWindowInternalLiteralCompleteRankEvenPhysicalChoiceProof (exact_SelectedLiteralCompleteRankEvenPhysicalScalar)
open NumberedWindowInternalOriginalRankedTupleProof (OriginalOutputScalar exact_OriginalRankedTuple)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralRankGuard (rankApplication)
open NumberedWindowInternalRankUniversalCarrier (completeRankEven alwaysCarried)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalNeutralRankApplicationReinstallTargets (selectRankInputs)
open NumberedWindowInternalProbeTargets (FreshVariablesComputable)
open NumberedWindowInternalPresentationTargets (data)

/-- Select all physical original numerical, application, and probe
programs in one rank-guarded body with a genuine carrier at every edge
destination. Retain the original unrefined tuple
and its raw report as separately identified old objects. The only
extra numerical law is the real output scalar of the chosen settings. -/
theorem exact_SelectedLiteralCompleteOriginalRankedChoice :
    ∃ (rankProg : Program 1) (C : Program 3),
      (∀ n, evaluate rankProg (n ::ᵥ nil) = rawRank n) ∧ ActualSelectedCoverOutput C ∧
    ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W → OriginalOutputScalar s →
      ∃ (cv tv syntaxProg : Program 1) (X : Program 2) (root other windowProg : Program 3)
          (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root xs s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s X ∧
        let raw := typedRaw5 root other windowProg syntaxProg
        let least := packedLeastProgram C X windowProg s
        let i := addressScalar cv tv windowProg least
        let g := addressRank rankProg
        let updated := frontendInputs i least v
        let final := selectRankInputs i g updated
        let R := addressPositive cv tv raw least
        let N := completeRankEven i g R
        CallbacksAt xs s cv tv raw least ∧
        ActualScalarCalibration s i ∧
        chosenA final = chosenA v ∧
        final.applicationGuard = rankApplication i g (guard i (applicationCore least)) ∧
        TupleAt xs s W i (jRaw i) R (dCore i R permutation) updated ∧
        InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
        TupleAt xs s W i (jRaw i) N (dCore i N permutation) final ∧
        (∀ c, FreshVariablesComputable (data i (jRaw i) N (dCore i N permutation))
          final.applicationGuard (chosenH final W) (chosenA final) c) ∧
        (∀ c, OriginalOddRules i R c ∧ OriginalOddRules i N c) := by
  obtain ⟨rankProg,C,rankFit,cover,choose⟩ := exact_SelectedLiteralCompleteRankEvenPhysicalScalar
  refine ⟨rankProg,C,rankFit,cover,?_⟩
  intro xs s W valid scalarOutput
  obtain ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps,guardEq,oldTuple,report,evenTuple,odd⟩ := choose xs s W valid
  let raw := typedRaw5 root other windowProg V
  let least := packedLeastProgram C X windowProg s
  let i := addressScalar cv tv windowProg least
  let g := addressRank rankProg
  let R := addressPositive cv tv raw least
  let N := completeRankEven i g R
  let update := frontendInputs i least v
  obtain ⟨keeps',guardEq',installed,fresh⟩ := exact_OriginalRankedTuple xs s W valid
    i (jRaw i) rankProg (alwaysCarried i R) (dCore i N permutation) update isc rankFit scalarOutput evenTuple
  have guarded := guardEq'.trans (congrArg (rankApplication i g) guardEq)
  exact ⟨cv,tv,V,X,root,other,windowProg,v,hroot,hother,hsyntax,hwindow,hX,
    callbacks,isc,keeps'.trans keeps,guarded,oldTuple,report,installed,fresh,odd⟩

#print axioms exact_SelectedLiteralCompleteOriginalRankedChoice
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCompleteOriginalRankedChoiceProof
