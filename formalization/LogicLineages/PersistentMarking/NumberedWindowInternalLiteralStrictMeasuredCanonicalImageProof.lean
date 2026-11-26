module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredImageTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoLeastLawsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRebuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredCanonicalImageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints exact_OpenLeastOnWindow)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (exact_OpenStrictMeasuredMemoTransport)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
open NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralApplicationRebuildProof (exact_OpenLiteralApplicationFromReportedLeast)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLiteralAppAddressReport (ctx ty q : OTerm α) :
    D B Γ (addressReport (addressTerm ctx ty q) ctx ty q) := by
  obtain ⟨⟨shell⟩,⟨c⟩,⟨t⟩,⟨k⟩⟩ :=
    NumberedWindowInternalAtomicRefinementObjectSelectorsProof.literalAddress (body := B) (Γ := Γ) ctx ty q
  exact ⟨Derivation.conjunctionIntroduction shell
    (Derivation.conjunctionIntroduction c (Derivation.conjunctionIntroduction t k))⟩

/-- Restore the very same full nested least reports and the original
application constructor at the canonical function and the untouched
original argument address, with the exact certified result supplied. -/
theorem exact_OpenStrictMeasuredReportedApplication (s : Settings) (X base : Program 2)
    (T V TV baseM cv tv : Program 1) (finite : List Nat)
    (ctx dom cod f₀ a₀ u y m : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let W := selectedBiAuxWindow s base T V TV baseM
    let Base := selectedBiAuxBase s X base T V TV baseM
    let E := recursiveTypedMemo Base
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) finite
    MemoSelectedReports C s Base →
    D B Γ (leastOnGraph C E s ctx cod (auxiliaryTerm dom cod f₀ a₀) m) →
    D B Γ (unary i (suc z) (addressTerm ctx (rawCons dom cod) f₀)) →
    D B Γ (unary i (suc z) u) →
    D B Γ (addressReport u ctx dom a₀) →
    D B Γ (eqn y (addressTerm ctx cod m)) →
    D B Γ (programGraph (applicationGuard i L) (suc z) ![addressTerm ctx (rawCons dom cod) f₀,u,y]) := by
  intro C W Base E L i selected parent fScalar uScalar arg result
  have full := selected B α Γ ctx cod (auxiliaryTerm dom cod f₀ a₀) m parent
  exact exact_OpenLiteralApplicationFromReportedLeast i L (addressTerm ctx (rawCons dom cod) f₀) u y
    ctx dom cod f₀ a₀ m (exact_OpenLiteralAppAddressReport ctx (rawCons dom cod) f₀)
    arg fScalar uScalar full result

#print axioms exact_OpenLiteralAppAddressReport
#print axioms exact_OpenStrictMeasuredReportedApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredCanonicalImageProof
