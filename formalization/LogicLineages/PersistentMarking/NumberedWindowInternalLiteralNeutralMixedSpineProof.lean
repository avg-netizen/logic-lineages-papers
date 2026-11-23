module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMixedDomainSpineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralArrowGroundFreshProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreshGroundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralMixedSpineProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral neutralWithCarrier)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowInternalPullbackTargets (ForwardRule Pullback)
open NumberedWindowInternalPullbackChecks (exact_InternalPullback)
open NumberedWindowInternalNeutralAuxiliaryFreshGroundProof (exact_LiteralNeutralGroundFresh)
open NumberedWindowInternalLiteralNeutralArrowGroundFreshProof (exact_OpenLiteralNeutralArrowGroundFresh)
open NumberedWindowInternalMixedDomainSpineProof
open NumberedWindowComputabilityFormulaTargets (formula)

theorem exact_LiteralNeutralMixedFresh (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i : Program 1) (r p : Program 3) (c : Nat) (v : Inputs)
    (sameP : v.applicationGuard = outputGuard i (refinedApplication p))
    (pack : TupleAt xs s W i (jRaw i) (augmented i (neutralWithCarrier i r))
      (dCore i (augmented i (neutralWithCarrier i r)) permutation) v) :
    MixedFreshAt (literalNeutral i r) v.applicationGuard (chosenH v W) (chosenA v) c := by
  intro σ τ permitted α Γ q u typed fresh
  cases permitted with
  | ground =>
    exact exact_LiteralNeutralGroundFresh xs s W i r v c pack τ α Γ q u typed fresh
  | arrowGround domain =>
    rw [sameP]
    exact exact_OpenLiteralNeutralArrowGroundFresh i r p c v W domain τ α Γ q u typed fresh

/-- The currently selected h really runs this same physical guarded
application p. Its true ForwardRule remains an explicit original-domain
input and is used to build object Pullback, not assumed or replaced. -/
theorem exact_LiteralNeutralMixedSpine (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i : Program 1) (r p : Program 3) (c : Nat) (v : Inputs)
    (sameP : v.applicationGuard = outputGuard i (refinedApplication p))
    (pack : TupleAt xs s W i (jRaw i) (augmented i (neutralWithCarrier i r))
      (dCore i (augmented i (neutralWithCarrier i r)) permutation) v)
    (forward : ForwardRule (literalNeutral i r) v.applicationGuard c)
    (τ : ProbeTy) (supported : MixedDomains τ) (α : Type) (Γ : List (Formula α)) (q : OTerm α)
    (typed : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (typedAt (chosenH v W) τ q)))
    (computable : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (formula v.applicationGuard τ q))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (membership false q)) := by
  let R := augmented i (neutralWithCarrier i r)
  let D := dCore i R permutation
  have guards := pack.2.2.2.2.2.1
  have total := pack.2.2.2.2.2.2.2.2.1
  have pullback : Pullback (literalNeutral i r) v.applicationGuard c :=
    exact_InternalPullback i (jRaw i) R D v.applicationGuard c guards forward
  exact exact_MixedSpineTypedComputabilityImpliesMembership _ _ _ _ c pullback (total c)
    (exact_LiteralNeutralMixedFresh xs s W i r p c v sameP pack) τ supported α Γ q typed computable

#print axioms exact_LiteralNeutralMixedFresh
#print axioms exact_LiteralNeutralMixedSpine
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralMixedSpineProof
