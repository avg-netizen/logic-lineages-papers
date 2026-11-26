module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedParentHopsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageRetapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedSelfLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAdvanceCoordinatesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (canonicalCoordinates)
open NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof (openTest)
open NumberedWindowInternalSparsePositiveWindowTargets (AdvanceWindows)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph actualCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalLiteralLeastOnFixedPointProof
  (WindowEndpoints exact_OpenLeastOnWindow exact_OpenLeastOnFixedPoint)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw exact_OpenSelectedJoinedRawWindows)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralJoinedParentHopsProof (exact_OpenRawWithTargetUnderlying)
open NumberedWindowInternalLiteralStrictImageRetapeProof (exact_OpenStrictFullPrimitiveReport)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator exact_FullAuxiliaryDecoratorOpen)
open NumberedWindowInternalLiteralGuardedSelfLeastProof (exact_OpenLiteralGuardedSelfLeast)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn rawWithTarget
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenMemoCanonicalCoordinate (C W : Program 3) (Base : Program 4) (s : Settings)
    (ctx ty q k : OTerm α) :
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    WindowEndpoints W E → Preserves E L₀ →
    D B Γ (windowAt W ctx ty q) → D B Γ (programGraph L (suc k) ![ctx,ty,q]) →
    D B Γ (windowAt (canonicalCoordinates W L) ctx ty k) := by
  intro E L₀ L ends stable window report
  have min := exact_OpenStrictFullPrimitiveReport L₀ ctx ty q k report
  obtain ⟨win⟩ := exact_OpenLeastOnWindow C E s W ends ctx ty q k min window
  have self := exact_OpenLeastOnFixedPoint C E s stable ctx ty q k min
  obtain ⟨fixed⟩ := exact_OpenLiteralGuardedSelfLeast (fullAuxiliaryDecorator L₀) ctx ty k
    (exact_FullAuxiliaryDecoratorOpen.self L₀ B α Γ ctx ty k self)
  obtain ⟨test⟩ := openTest W L B α Γ ctx ty k
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight test)
    (Derivation.conjunctionIntroduction win fixed)⟩

/-- The original nonempty path admits this local guard law on BOTH
actual canonical coordinates, without assuming either scalar address. -/
theorem exact_OpenJoinedAdvanceCoordinates (s : Settings) (X base : Program 2)
    (T V TV baseM i cv tv : Program 1) (leaf : Nat → Program 3) (other : Program 3) :
    let C := measuredStrictCover V TV baseM
    let W := joinedAuxiliaryWindow s base T V TV baseM
    let Base := joinedBiAuxBase s X base T V TV baseM
    let E := recursiveTypedMemo Base
    let L := memoFilteredLeast C Base s
    let raw := selectedJoinedRaw s base T V TV baseM leaf other
    let R := rawWithTarget i cv tv raw L
    WindowEndpoints W E → Preserves E (packedLeastOn C E s) →
    AdvanceWindows R L (canonicalCoordinates W L) := by
  intro C W Base E L raw R ends stable B α Γ ctx ty src hop dst
  let input := selectedGraph R L (suc dst) ctx ty (suc src) hop
  let Δ := input :: Γ
  have h : Derivation B Δ input := Derivation.hypothesis List.mem_cons_self
  obtain ⟨opened⟩ := exact_OpenSuccessfulAdvanceCalls B R L α ctx ty src hop dst
  have reports := closedApply ⟨Derivation.conjunctionLeft opened⟩ ⟨h⟩
  have out : D B Δ (windowAt (canonicalCoordinates W L) ctx ty src ⊓ windowAt (canonicalCoordinates W L) ctx ty dst) := by
    apply reportCases R L ctx ty src hop dst _ reports
    intro β j Θ q w r keep row
    rw [conjunctionRename,windowRename,windowRename]
    obtain ⟨facts⟩ := row
    let c := ctx.relabel j
    let t := ty.relabel j
    let pair := Derivation.conjunctionRight facts
    have rawStep := exact_OpenRawWithTargetUnderlying i cv tv raw L c t q w r ⟨Derivation.conjunctionLeft pair⟩
    obtain ⟨wq,wr⟩ := exact_OpenSelectedJoinedRawWindows s base T V TV baseM leaf other c t q w r rawStep
    let values := Derivation.conjunctionRight pair
    obtain ⟨start⟩ := exact_OpenMemoCanonicalCoordinate C W Base s c t q (src.relabel j)
      ends stable wq ⟨Derivation.conjunctionLeft values⟩
    obtain ⟨finish⟩ := exact_OpenMemoCanonicalCoordinate C W Base s c t r (dst.relabel j)
      ends stable wr ⟨Derivation.conjunctionRight values⟩
    exact ⟨Derivation.conjunctionIntroduction start finish⟩
  obtain ⟨out⟩ := out
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_OpenMemoCanonicalCoordinate
#print axioms exact_OpenJoinedAdvanceCoordinates
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAdvanceCoordinatesProof
