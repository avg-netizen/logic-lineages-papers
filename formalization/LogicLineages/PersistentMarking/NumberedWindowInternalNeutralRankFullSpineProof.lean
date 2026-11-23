module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankFreshProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalProbeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankFullSpineProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralRankGuard (rankEven rankApplication)
open NumberedWindowInternalNeutralRankFreshProof (exact_RankGuardedTypedFresh)
open NumberedWindowInternalProbeTargets (typedAt)
open NumberedWindowInternalProbeChecks (exact_TypedComputabilityImpliesMembership)
open NumberedWindowInternalPullbackTargets (ForwardRule)
open NumberedWindowInternalPullbackChecks (exact_InternalPullback)
open NumberedWindowComputabilityFormulaTargets (formula)

/-- No restriction on the input type now remains. The fresh-C premise is
paid by the genuine ranked even and application programs in the chosen
new tuple. The actual same-program forward image is still explicit. -/
theorem exact_RankGuardedTypedComputabilityImpliesI (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i j raw : Program 1) (r d p : Program 3) (v : Inputs) (c : Nat)
    (pack : TupleAt xs s W i j (rankEven i (addressRank raw) r) d v)
    (pdef : v.applicationGuard = rankApplication i (addressRank raw) p)
    (forward : ForwardRule (data i j (rankEven i (addressRank raw) r) d) v.applicationGuard c) :
    ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
      let S := data i j (rankEven i (addressRank raw) r) d
      let B := sourceBody S c
      Nonempty (Derivation B Γ (typedAt (chosenH v W) τ q)) →
      Nonempty (Derivation B Γ (formula v.applicationGuard τ q)) →
      Nonempty (Derivation B Γ (membership false q)) := by
  have fresh := exact_RankGuardedTypedFresh xs s W i j raw r d p v c pack pdef
  obtain ⟨_,_,_,_,_,guards,_,_,total,_,_⟩ := pack
  let R := rankEven i (addressRank raw) r
  let S := data i j R d
  exact exact_TypedComputabilityImpliesMembership S v.applicationGuard (chosenH v W) (chosenA v) c
    (exact_InternalPullback i j R d v.applicationGuard c guards forward) (total c) fresh

#print axioms exact_RankGuardedTypedComputabilityImpliesI
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankFullSpineProof
