module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoTypedAuxCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoInputsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalInstallationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoTypedAuxInstalledProof
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
open NumberedWindowInternalLiteralSyntaxMemoWindow (window)
open NumberedWindowInternalLiteralSyntaxMemoInputsProof
  (exact_SyntaxMemoIntrinsicInput exact_SyntaxMemoTypeInput)
open NumberedWindowInternalLiteralSyntaxMemoWindowNumericProof (exact_SyntaxMemoWindow)
open NumberedWindowInternalLiteralMemoTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalOriginalFirstHopCoreProof (D oneHopProgram)
open NumberedWindowInternalOriginalFirstHopAddressProof (exact_OrdinaryFirstHop)
open NumberedWindowInternalNeutralFactsTargets (firstHop)

structure Packet (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i cv tv : Program 1) (leaf : Nat → Program 3) (other : Program 3) (base : Program 2)
    (T V : Program 1) (least p₀ : Program 3) (v : Inputs) : Prop where
  fit : LeafFit (fixed xs s.window.2) (leafAtAuxiliary leaf)
  fallbackFit : ActualFallback (auxiliaryFallback (fallback other))
  syntaxFit : ActualRawSyntax V
  windowFit : ActualPackedWindow s (window base T V)
  physical : let raw := ActiveRaw leaf other base T V
    let r := addressPositive cv tv raw least
    InstalledTupleAt xs s W i (jRaw i) cv tv (dCore i r permutation) p₀ raw least v
  first : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    let r := addressPositive cv tv (ActiveRaw leaf other base T V) least
    let S := literalData i r
    D (sourceBody S c) Γ (edge S false c x y) → D (sourceBody S c) Γ (firstHop S (oneHopProgram r) c x y)

/-- Genuine selected same-context guard transport in the original
ValidWindow body. The newly chosen raw program does not change the
numeric result of any original callback. -/
theorem exact_ConcreteMemoTypedAuxTuple (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) :
    ∃ (i cv tv : Program 1) (leaf : Nat → Program 3) (other : Program 3) (base : Program 2)
      (T V : Program 1) (least p₀ : Program 3) (v : Inputs),
        Packet xs s W i cv tv leaf other base T V least p₀ v := by
  obtain ⟨i,cv,tv,leaf,other,oldWindow,V,least,p₀,v,old⟩ :=
    exact_ConcreteAuxiliaryOwnFuelTuple xs s W valid
  obtain ⟨base,hb⟩ := exact_SyntaxMemoIntrinsicInput s oldWindow old.windowFit
  obtain ⟨T,ht⟩ := exact_SyntaxMemoTypeInput s
  let oldRaw := NumberedWindowInternalLiteralAuxOwnFuelInstalledProof.Raw leaf other oldWindow V
  let oldD := dCore i (addressPositive cv tv oldRaw least) permutation
  let raw := ActiveRaw leaf other base T V
  let win := window base T V
  let active := leafAtAuxiliary leaf
  have leafFit := exact_AuxiliaryLeafFit xs s.window.2 leaf old.fit
  have rootFit : ActualRoot (NumberedWindowConcreteCheckers.root xs s) (root active) :=
    exact_LiteralRootNumeric (fixed xs s.window.2) active leafFit
  have hw : ActualPackedWindow s win := exact_SyntaxMemoWindow s base T V hb ht old.syntaxFit
  have cal := exact_TypedRaw5Calibration xs s (root active) (auxiliaryFallback (fallback other)) win V
    rootFit old.fallbackFit old.syntaxFit hw
  have next := exact_ReinstallCalibratedRawTuple xs s W valid i (jRaw i) cv tv oldD
    p₀ oldRaw raw least v old.physical cal
  have installed := (exact_ReinstallPhysicalLiteralMultisets xs s W valid i (jRaw i) cv tv oldD
    p₀ raw least v next).1
  exact ⟨i,cv,tv,leaf,other,base,T,V,least,p₀,v,leafFit,old.fallbackFit,
    old.syntaxFit,hw,installed,fun c α Γ x y => exact_OrdinaryFirstHop i cv tv raw least c α Γ x y⟩

#print axioms exact_ConcreteMemoTypedAuxTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoTypedAuxInstalledProof
