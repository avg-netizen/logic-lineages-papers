module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedMemoPacketProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMemoTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedCanonicalChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageRetapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCarrierChildHopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedPathHopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseAddressSingletonCoreProof (fromCalls)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (provide)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (ParentTypeEvidence)
open NumberedWindowInternalLiteralBiAuxWindowLiftProof (exact_OpenJoinedWindowAssembly)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralBiAuxMemoTransportProof (exact_OpenBiAuxMemoTransport)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof (varyAuxiliary)
open NumberedWindowInternalLiteralMemoVaryingParentProof (varyingOperandType)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralEnrichedCanonicalChildProof (exact_OpenEnrichedCanonicalChild)
open NumberedWindowInternalLiteralCarrierChildHopProof (exact_OpenRawWithTargetIntro)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralStrictImageRetapeProof (exact_OpenStrictFullPrimitiveReport)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn rawWithTarget
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Transport the parent minimum along the exact child class report read
from the positive checker's own full least call. -/
theorem exact_OpenJoinedFunctionRepresentative (s : Settings) (X base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod arg q f value : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let W := joinedAuxiliaryWindow s base T V TV baseM
    let Base := joinedBiAuxBase s X base T V TV baseM
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    CanReverse Base → Preserves E L₀ → ParentTypeEvidence s T TV B Γ dom cod →
    D B Γ (windowAt W ctx dom arg) →
    D B Γ (programGraph L (suc f) ![ctx,rawCons dom cod,q]) →
    D B Γ (leastOnGraph C E s ctx cod (auxiliaryTerm dom cod q arg) value) →
    D B Γ (leastOnGraph C E s ctx cod (auxiliaryTerm dom cod f arg) value) := by
  intro C W Base E L₀ L reverse stable types fixed report parent
  have arrow (d c : OTerm α) : varyingOperandType false d c = rawCons d c := rfl
  have input (d c : OTerm α) : varyingOperandType true d c = d := rfl
  have frame (d c q a : OTerm α) : varyAuxiliary false d c q a = auxiliaryTerm d c q a := rfl
  have child := exact_OpenStrictFullPrimitiveReport L₀ ctx (rawCons dom cod) q f report
  have l : D B Γ (leastOnGraph C E s ctx (varyingOperandType false dom cod) q f) := by rw [arrow]; exact child
  have a : D B Γ (windowAt W ctx (varyingOperandType true dom cod) arg) := by rw [input]; exact fixed
  have p : D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary false dom cod q arg) value) := by rw [frame]; exact parent
  have result := exact_OpenBiAuxMemoTransport s X T V TV baseM W (exact_OpenJoinedWindowAssembly s base T V TV baseM)
    false ctx dom cod q f arg value reverse stable types a l p
  rw [frame] at result
  exact result

/-- Exact, genuinely positive singleton on the original positive fold,
including the finite canonical target gate of the wrapped checker. -/
theorem exact_OpenJoinedPositiveAtParents (s : Settings) (X base : Program 2) (T V TV baseM cv tv : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (finite : List Nat)
    (ctx cod q w r a b : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let W := joinedAuxiliaryWindow s base T V TV baseM
    let Base := joinedBiAuxBase s X base T V TV baseM
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) finite
    let raw := selectedJoinedRaw s base T V TV baseM leaf other
    let R := rawWithTarget i cv tv raw L
    WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) cod) →
    D B Γ (literalMembership finite cod) → D B Γ (windowAt W ctx cod r) →
    D B Γ (programGraph raw (suc z) ![ctx,cod,q,w,r]) →
    D B Γ (leastOnGraph C E s ctx cod q a) → D B Γ (leastOnGraph C E s ctx cod r b) →
    D B Γ (supplied R L ctx cod a b) := by
  intro C W Base E L₀ L i raw R ends stable selected gc gt finiteTy formed child src dst
  have right := selected B α Γ ctx cod r b dst
  have left := selected B α Γ ctx cod q a src
  have scalar := exact_OpenEnrichedCanonicalChild cv tv C W E s finite ctx cod r b ends stable gc gt finiteTy formed dst
  obtain ⟨step⟩ := exact_OpenRawWithTargetIntro i cv tv raw L ctx cod q w r b gc gt right child scalar
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  have calls : D B Γ (actualCalls R L ctx cod a b q w r) :=
    ⟨Derivation.conjunctionIntroduction step (Derivation.conjunctionIntroduction left right)⟩
  exact provide R L ctx cod a b (singletonCertificate b q w r) (fromCalls R L ctx cod a b q w r calls)

#print axioms exact_OpenJoinedFunctionRepresentative
#print axioms exact_OpenJoinedPositiveAtParents
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedPathHopProof
