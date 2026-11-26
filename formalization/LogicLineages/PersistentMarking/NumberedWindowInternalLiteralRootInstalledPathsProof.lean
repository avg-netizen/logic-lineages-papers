module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootPayloadProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalOneHopInversionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInstalledJCharacterizationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootInstalledPathsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge carrier membership)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowRootDispatchAlgorithm (fixed)
open NumberedWindowInternalLiteralRootDispatchNumericProof (LeafFit root)
open NumberedWindowInternalLiteralRootTypedRawProof (exact_ConcreteLiteralRootRaw5)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseTypedRawInstallationChecks
  (exact_ReinstallCalibratedRawTuple exact_ConcreteSparseTypedRawInstalledTuple)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualFallback)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalNeutralFactsTargets (firstHop)
open NumberedWindowInternalOriginalFirstHopCoreProof (D oneHopProgram)
open NumberedWindowInternalOriginalFirstHopAddressProof (exact_OrdinaryFirstHop)
open NumberedWindowInternalLiteralPhysicalInstallationProof (exact_ReinstallPhysicalLiteralMultisets)
open NumberedWindowInternalLiteralPresentationReinstallProof (exact_ReinstalledLiteralTupleAndJ)
open NumberedWindowInternalLiteralRawMembersJProof (allRawMembers)
open NumberedWindowInternalLiteralEndpointInstallationProof (LiteralEndpointPacket)
open NumberedWindowInternalLiteralEndpointSingletonProof (exact_EndpointRefinedLiteralSingletonIff)
open NumberedWindowInternalLiteralJCharacterizationProof (exact_EndpointLiteralJCharacterization)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementTupleChecks (exact_ReinstallEndpointRefinedTuple)
open NumberedWindowInternalPositiveEndpointRefinementReportChecks (exact_InstalledEndpointRefinedReport)

abbrev Raw (leaf : Nat → Program 3) (other window : Program 3) (syntaxCheck : Program 1) :=
  typedRaw5 (root leaf) other window syntaxCheck

/-- Same actual checked source window, both physical literal presentations.
The ordinary body has exact first-hop decomposition; the endpoint-
guarded body has the exact J characterization. No equality of proof
trees across those distinct bodies is claimed. -/
structure Packet (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i cv tv : Program 1) (leaf : Nat → Program 3) (other window : Program 3)
    (syntaxCheck : Program 1) (least p₀ : Program 3) (v : Inputs) : Prop where
  calibratedLeaves : LeafFit (fixed xs s.window.2) leaf
  fallback : ActualFallback other
  syntaxFit : ActualRawSyntax syntaxCheck
  windowFit : ActualPackedWindow s window
  ordinary : let raw := Raw leaf other window syntaxCheck
    let r := addressPositive cv tv raw least
    InstalledTupleAt xs s W i (jRaw i) cv tv (dCore i r permutation) p₀ raw least v
  first : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    let raw := Raw leaf other window syntaxCheck
    let r := addressPositive cv tv raw least
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (edge S false c x y) → D B Γ (firstHop S (oneHopProgram r) c x y)
  endpoint : LiteralEndpointPacket xs s W i cv tv (Raw leaf other window syntaxCheck) least p₀ v
  rawJ : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (m : OTerm α),
    let r := withEndpointCarriers i (addressPositive cv tv (Raw leaf other window syntaxCheck) least)
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (membership true m) ↔ D B Γ (carrier S true c m) ∧ D B Γ (allRawMembers m)

theorem exact_ConcreteLiteralRootAndPaths (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) :
    ∃ (i cv tv : Program 1) (leaf : Nat → Program 3) (other window : Program 3)
      (syntaxCheck : Program 1) (least p₀ : Program 3) (v : Inputs),
      Packet xs s W i cv tv leaf other window syntaxCheck least p₀ v := by
  obtain ⟨i,j,cv,tv,d,p₀,oldRaw,least,v,_,other,window,syntaxCheck,old,_,fallback,syntaxFit,windowFit,_⟩ :=
    exact_ConcreteSparseTypedRawInstalledTuple xs s W valid
  obtain ⟨leaf,fit,_,cal⟩ :=
    exact_ConcreteLiteralRootRaw5 xs s other window syntaxCheck fallback syntaxFit windowFit
  let raw := Raw leaf other window syntaxCheck
  let r := addressPositive cv tv raw least
  have new : InstalledTupleAt xs s W i j cv tv d p₀ raw least v :=
    exact_ReinstallCalibratedRawTuple xs s W valid i j cv tv d p₀ oldRaw raw least v old cal
  have ordinary := (exact_ReinstallPhysicalLiteralMultisets xs s W valid i j cv tv d p₀ raw least v new).1
  have guarded := exact_ReinstallEndpointRefinedTuple xs s W valid i j r d v new.1
  let r₁ := withEndpointCarriers i r
  obtain ⟨refined,union⟩ := exact_ReinstalledLiteralTupleAndJ xs s W valid i j r₁ d v guarded
  have endpoint : LiteralEndpointPacket xs s W i cv tv raw least p₀ v :=
    ⟨refined,new.2.1,new.2.2.1,
      fun c α x w y => exact_InstalledEndpointRefinedReport i (jRaw i) cv tv (dCore i r₁ permutation)
        raw least c α x w y,
      fun c α Γ q => exact_EndpointRefinedLiteralSingletonIff i r c α Γ q,union⟩
  exact ⟨i,cv,tv,leaf,other,window,syntaxCheck,least,p₀,v,fit,fallback,syntaxFit,windowFit,ordinary,
    fun c α Γ x y => exact_OrdinaryFirstHop i cv tv raw least c α Γ x y,
    endpoint,fun c α Γ m => exact_EndpointLiteralJCharacterization i r c α Γ m⟩

#print axioms exact_ConcreteLiteralRootAndPaths
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootInstalledPathsProof
