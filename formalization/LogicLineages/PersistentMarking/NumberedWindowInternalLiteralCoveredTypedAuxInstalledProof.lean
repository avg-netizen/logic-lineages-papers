module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoInputsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalInstallationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxInstalledProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowRootDispatchAlgorithm (fixed)
open NumberedWindowInternalLiteralRootDispatchNumericProof (LeafFit root exact_LiteralRootNumeric)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseTypedRawChecks (exact_TypedRaw5Calibration)
open NumberedWindowInternalSparseTypedRawInstallationChecks (exact_ReinstallCalibratedRawTuple)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalLiteralPhysicalInstallationProof (exact_ReinstallPhysicalLiteralMultisets)
open NumberedWindowInternalLiteralAuxOwnFuelInstalledProof (exact_ConcreteAuxiliaryOwnFuelTuple)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralAuxRootLeafFitProof (exact_AuxiliaryLeafFit)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow WindowSeedsCovered)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseCoverScratchNumericChecks (exact_SelectedCoverToScratch)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseScalarEdgeNumericChecks (exact_SelectedPackedScalarEdge)
open NumberedWindowInternalSparsePackedLeastNumericChecks (exact_PackedLeastComposition)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_ReinstallCalibratedLeast)
open NumberedWindowInternalSparseApplicationReinstallChecks (exact_ReinstallGuardedApplicationTuple)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalLiteralSyntaxMemoInputsProof
  (exact_SyntaxMemoIntrinsicInput exact_SyntaxMemoTypeInput)
open NumberedWindowInternalLiteralCoveredMemoNumericProof (exact_CoveredMemoWindow)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalOriginalFirstHopCoreProof (D oneHopProgram)
open NumberedWindowInternalOriginalFirstHopAddressProof (exact_OrdinaryFirstHop)
open NumberedWindowInternalNeutralFactsTargets (firstHop)

structure Packet (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (X base : Program 2)
    (T V : Program 1) (v : Inputs) : Prop where
  fit : LeafFit (fixed xs s.window.2) (leafAtAuxiliary leaf)
  fallbackFit : ActualFallback (auxiliaryFallback (fallback other))
  syntaxFit : ActualRawSyntax V
  windowFit : ActualPackedWindow s (coveredMemoWindow C s base T V)
  coverFit : ActualSelectedCoverOutput C
  exchangeFit : ActualTermExchange s X
  leastFit : ActualLeastCalibration s (packedLeastProgram C X (coveredMemoWindow C s base T V) s)
  physical : let raw := ActiveRaw C s leaf other base T V
    let least := packedLeastProgram C X (coveredMemoWindow C s base T V) s
    let r := addressPositive cv tv raw least
    InstalledTupleAt xs s W i (jRaw i) cv tv (dCore i r permutation) (applicationCore least) raw least v
  first : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    let least := packedLeastProgram C X (coveredMemoWindow C s base T V) s
    let r := addressPositive cv tv (ActiveRaw C s leaf other base T V) least
    let S := literalData i r
    D (sourceBody S c) Γ (edge S false c x y) → D (sourceBody S c) Γ (firstHop S (oneHopProgram r) c x y)

/-- The selected raw, packed least, and application frontend all use the
same actual window. The extra numeric hypothesis is exactly original
finite-cover seed occurrence, not general scalar accessibility. -/
theorem exact_ConcreteCoveredTypedAuxTuple (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (seeds : WindowSeedsCovered s) :
    ∃ (i cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (X base : Program 2)
      (T V : Program 1) (v : Inputs),
        Packet xs s W i cv tv leaf C other X base T V v := by
  obtain ⟨i,cv,tv,leaf,other,oldWindow,V,oldLeast,p₀,v,old⟩ :=
    exact_ConcreteAuxiliaryOwnFuelTuple xs s W valid
  obtain ⟨C,cover,_⟩ := exact_SelectedCoverToScratch
  obtain ⟨X,_,exchange,_,_⟩ := exact_SelectedPackedScalarEdge s
  obtain ⟨base,hb⟩ := exact_SyntaxMemoIntrinsicInput s oldWindow old.windowFit
  obtain ⟨T,ht⟩ := exact_SyntaxMemoTypeInput s
  let oldRaw := NumberedWindowInternalLiteralAuxOwnFuelInstalledProof.Raw leaf other oldWindow V
  let oldD := dCore i (addressPositive cv tv oldRaw oldLeast) permutation
  let raw := ActiveRaw C s leaf other base T V
  let win := coveredMemoWindow C s base T V
  let least := packedLeastProgram C X win s
  let active := leafAtAuxiliary leaf
  have leafFit := exact_AuxiliaryLeafFit xs s.window.2 leaf old.fit
  have rootFit : ActualRoot (NumberedWindowConcreteCheckers.root xs s) (root active) :=
    exact_LiteralRootNumeric (fixed xs s.window.2) active leafFit
  have hw : ActualPackedWindow s win := by
    exact exact_CoveredMemoWindow C s base T V cover seeds hb ht old.syntaxFit
  have cal := exact_TypedRaw5Calibration xs s (root active) (auxiliaryFallback (fallback other)) win V
    rootFit old.fallbackFit old.syntaxFit hw
  have hl := exact_PackedLeastComposition s C X win cover exchange hw
  have newRaw := exact_ReinstallCalibratedRawTuple xs s W valid i (jRaw i) cv tv oldD
    p₀ oldRaw raw oldLeast v old.physical cal
  have newLeast := exact_ReinstallCalibratedLeast xs s W valid i (jRaw i) cv tv oldD p₀
    raw oldLeast least v newRaw hl
  have app := (exact_ReinstallGuardedApplicationTuple xs s W valid i (jRaw i) cv tv oldD p₀
    raw least v newLeast).2
  let updated := frontendInputs i least v
  have installed := (exact_ReinstallPhysicalLiteralMultisets xs s W valid i (jRaw i) cv tv oldD
    (applicationCore least) raw least updated app).1
  exact ⟨i,cv,tv,leaf,C,other,X,base,T,V,updated,leafFit,old.fallbackFit,old.syntaxFit,hw,
    cover,exchange,hl,installed,fun c α Γ x y => exact_OrdinaryFirstHop i cv tv raw least c α Γ x y⟩

#print axioms exact_ConcreteCoveredTypedAuxTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxInstalledProof
