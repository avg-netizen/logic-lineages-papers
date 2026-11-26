module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalInstallationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEndpointSingletonProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEndpointInstallationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalSparseTuple (CallbacksAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowGuardedGraphTargets (guard)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalLiteralPresentationReinstallProof (exact_ReinstalledLiteralTupleAndJ)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalFunctionalRawUnion (functionalUnion)
open ConditionalJUnionTargets (CarrierUnion UnionClosure)
open NumberedWindowInternalScalarSingletonInductionProof (singletonJ)
open NumberedWindowInternalLiteralSingletonCarrierReflectionProof (D)
open NumberedWindowInternalLiteralEndpointSingletonProof
  (exact_EndpointRefinedLiteralSingletonIff)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementTupleChecks (exact_ConcreteEndpointRefinedInstalledTuple)
open NumberedWindowInternalPositiveEndpointRefinementReportTargets (guardedReport)
open NumberedWindowInternalPositiveEndpointRefinementReportChecks (exact_InstalledEndpointRefinedReport)

abbrev selectedR (i cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  withEndpointCarriers i (addressPositive cv tv raw least)

/-- The complete selected tuple on one exact body, with literal multiset
programs, endpoint guards, unchanged scalar and application choices,
and the new same-body J facts. -/
structure LiteralEndpointPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i cv tv : Program 1) (raw : Program 5) (least p₀ : Program 3) (v : Inputs) : Prop where
  tuple : let r := selectedR i cv tv raw least
    TupleAt xs s W i (jRaw i) r (dCore i r permutation) v
  application : v.applicationGuard = guard i p₀
  callbacks : CallbacksAt xs s cv tv raw least
  report : ∀ (c : Nat) (α : Type) (x w y : OTerm α),
    let r := selectedR i cv tv raw least
    let accept := accepts r x w y
    let checked := guardedReport i cv tv raw least x w y
    D (sourceBody (literalData i r) c) [] ((accept.imp checked) ⊓ (checked.imp accept))
  singleton : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    let B := sourceBody (literalData i (selectedR i cv tv raw least)) c
    D B Γ (singletonJ q) ↔ D B Γ (membership false q)
  union : ∀ c, let S := literalData i (selectedR i cv tv raw least)
    CarrierUnion S c functionalUnion ∧ UnionClosure S c functionalUnion

theorem exact_ConcreteLiteralEndpointPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) :
    ∃ (i cv tv : Program 1) (raw : Program 5) (least p₀ : Program 3) (v : Inputs),
      LiteralEndpointPacket xs s W i cv tv raw least p₀ v := by
  obtain ⟨i,j,cv,tv,d,p₀,raw,least,v,original,guarded⟩ :=
    exact_ConcreteEndpointRefinedInstalledTuple xs s W valid
  let r := selectedR i cv tv raw least
  obtain ⟨literal,J⟩ := exact_ReinstalledLiteralTupleAndJ xs s W valid i j r d v guarded
  refine ⟨i,cv,tv,raw,least,p₀,v,⟨literal,original.2.1,original.2.2.1,?_,?_,J⟩⟩
  · intro c α x w y
    exact exact_InstalledEndpointRefinedReport i (jRaw i) cv tv (dCore i r permutation) raw least c α x w y
  · intro c α Γ q
    exact exact_EndpointRefinedLiteralSingletonIff i (addressPositive cv tv raw least) c α Γ q

#print axioms exact_ConcreteLiteralEndpointPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEndpointInstallationProof
