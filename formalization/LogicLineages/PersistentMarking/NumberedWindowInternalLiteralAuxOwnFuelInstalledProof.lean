module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootInstalledPathsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalInstallationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelInstalledProof
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
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_TypedRaw5Calibration)
open NumberedWindowInternalSparseTypedRawInstallationChecks (exact_ReinstallCalibratedRawTuple)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalLiteralPhysicalInstallationProof (exact_ReinstallPhysicalLiteralMultisets)
open NumberedWindowInternalLiteralRootInstalledPathsProof (exact_ConcreteLiteralRootAndPaths)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralBoundedFallbackNumericProof (exact_DescendingFallback)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralAuxRootLeafFitProof (exact_AuxiliaryLeafFit)
open NumberedWindowInternalLiteralAuxFallbackNumericProof (exact_AuxiliaryFallback)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalOriginalFirstHopCoreProof (D oneHopProgram)
open NumberedWindowInternalOriginalFirstHopAddressProof (exact_OrdinaryFirstHop)
open NumberedWindowInternalNeutralFactsTargets (firstHop)

abbrev Raw (leaf : Nat → Program 3) (other window : Program 3) (syntaxCheck : Program 1) :=
  typedRaw5 (root (leafAtAuxiliary leaf)) (auxiliaryFallback (fallback other)) window syntaxCheck

/-- One original-body installation of the physically transparent
auxiliary checker with verified own-witness fuel. Its ordinary direct path is the same earlier exact
first-step construction at the newly selected raw program. -/
structure Packet (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i cv tv : Program 1) (leaf : Nat → Program 3) (other window : Program 3)
    (syntaxCheck : Program 1) (least p₀ : Program 3) (v : Inputs) : Prop where
  fit : LeafFit (fixed xs s.window.2) leaf
  fallbackFit : ActualFallback (auxiliaryFallback (fallback other))
  syntaxFit : ActualRawSyntax syntaxCheck
  windowFit : ActualPackedWindow s window
  physical : let raw := Raw leaf other window syntaxCheck
    let r := addressPositive cv tv raw least
    InstalledTupleAt xs s W i (jRaw i) cv tv (dCore i r permutation) p₀ raw least v
  first : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    let r := addressPositive cv tv (Raw leaf other window syntaxCheck) least
    let S := literalData i r
    D (sourceBody S c) Γ (edge S false c x y) → D (sourceBody S c) Γ (firstHop S (oneHopProgram r) c x y)

theorem exact_ConcreteAuxiliaryOwnFuelTuple (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) :
    ∃ (i cv tv : Program 1) (leaf : Nat → Program 3) (other window : Program 3)
      (syntaxCheck : Program 1) (least p₀ : Program 3) (v : Inputs),
        Packet xs s W i cv tv leaf other window syntaxCheck least p₀ v := by
  obtain ⟨i,cv,tv,leaf,other,window,syntaxCheck,least,p₀,v,old⟩ :=
    exact_ConcreteLiteralRootAndPaths xs s W valid
  let oldRaw := NumberedWindowInternalLiteralRootInstalledPathsProof.Raw leaf other window syntaxCheck
  let oldD := dCore i (addressPositive cv tv oldRaw least) permutation
  let raw := Raw leaf other window syntaxCheck
  let F := auxiliaryFallback (fallback other)
  let active := leafAtAuxiliary leaf
  have fallbackFit : ActualFallback F := exact_AuxiliaryFallback (fallback other) (exact_DescendingFallback other old.fallback)
  have leafFit := exact_AuxiliaryLeafFit xs s.window.2 leaf old.calibratedLeaves
  have rootFit : ActualRoot (NumberedWindowConcreteCheckers.root xs s) (root active) :=
    exact_LiteralRootNumeric (fixed xs s.window.2) active leafFit
  have cal := exact_TypedRaw5Calibration xs s (root active) F window syntaxCheck
    rootFit fallbackFit old.syntaxFit old.windowFit
  have next := exact_ReinstallCalibratedRawTuple xs s W valid i (jRaw i) cv tv oldD
    p₀ oldRaw raw least v old.ordinary cal
  have installed := (exact_ReinstallPhysicalLiteralMultisets xs s W valid i (jRaw i) cv tv oldD
    p₀ raw least v next).1
  exact ⟨i,cv,tv,leaf,other,window,syntaxCheck,least,p₀,v,old.calibratedLeaves,fallbackFit,
    old.syntaxFit,old.windowFit,installed,fun c α Γ x y => exact_OrdinaryFirstHop i cv tv raw least c α Γ x y⟩

#print axioms exact_ConcreteAuxiliaryOwnFuelTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelInstalledProof
