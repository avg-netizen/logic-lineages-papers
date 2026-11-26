module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredAuxWindowIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow packedWindow)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredParentWindowProof (exact_OpenStrictMeasuredParentWindow)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (selectedBiAuxWindow ParentTypeEvidence)
open NumberedWindowInternalLiteralCoveredAuxWindowIntroProof (exact_OpenCoveredAuxWindowIntro)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev selectedBiAuxCoveredWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1) : Program 3 :=
  coveredMemoWindow (measuredStrictCover V TV baseM) s base T (unitAuxSyntax V TV)

def joinedAuxiliaryWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1) : Program 3 :=
  conjunction (selectedBiAuxWindow s base T V TV baseM) (selectedBiAuxCoveredWindow s base T V TV baseM)

theorem exact_OpenJoinedAuxiliaryWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx ty q : OTerm α) :
    D B Γ (windowAt (joinedAuxiliaryWindow s base T V TV baseM) ctx ty q) ↔
    D B Γ (windowAt (selectedBiAuxWindow s base T V TV baseM) ctx ty q) ∧
      D B Γ (windowAt (selectedBiAuxCoveredWindow s base T V TV baseM) ctx ty q) := by
  let a := selectedBiAuxWindow s base T V TV baseM
  let b := selectedBiAuxCoveredWindow s base T V TV baseM
  constructor
  · intro h
    obtain ⟨c⟩ := conjunctionRecover a b ![ctx,ty,q] h
    exact ⟨⟨Derivation.conjunctionLeft c⟩,⟨Derivation.conjunctionRight c⟩⟩
  · rintro ⟨f,g⟩
    exact conjunctionAccept a b ![ctx,ty,q] f g

theorem exact_LiteralJoinedAuxiliaryWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (first : ActualPackedWindow s (selectedBiAuxWindow s base T V TV baseM))
    (second : ActualPackedWindow s (selectedBiAuxCoveredWindow s base T V TV baseM)) :
    ActualPackedWindow s (joinedAuxiliaryWindow s base T V TV baseM) := by
  intro c t q
  rw [joinedAuxiliaryWindow,actualConjunctionEvaluation,first c t q,second c t q]
  cases packedWindow s c t q <;> decide

/-- The same two joined child reports reconstruct both original window
computations at the parent. In particular, the covered raw window and
the strict measured window are not identified by numeric calibration. -/
theorem exact_OpenJoinedAuxiliaryParent (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let Va := unitAuxSyntax V TV
    let Q := joinedAuxiliaryWindow s base T V TV baseM
    ParentTypeEvidence s T TV B Γ dom cod →
    D B Γ (windowAt Q ctx (rawCons dom cod) fn) → D B Γ (windowAt Q ctx dom arg) →
    D B Γ (windowAt Q ctx cod (auxiliaryTerm dom cod fn arg)) ∧
      D B Γ (unary Va (suc z) (auxiliaryTerm dom cod fn arg)) := by
  intro C Va Q types f a
  obtain ⟨f₁,⟨f₂⟩⟩ := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx (rawCons dom cod) fn).mp f
  obtain ⟨a₁,⟨a₂⟩⟩ := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx dom arg).mp a
  obtain ⟨parent,live⟩ := exact_OpenStrictMeasuredParentWindow s base T V TV baseM ctx dom cod fn arg
    f₁ a₁ types.typed types.wellFormed types.domain types.codomain
  let p := auxiliaryTerm dom cod fn arg
  have cover := ((exact_OpenSealedWindow C s (strictAuxWindow base T) ctx cod p).1 parent).2
  obtain ⟨t⟩ := types.typed
  have ready := exact_OpenCoveredAuxWindowIntro C s base T Va ctx dom cod fn arg
    ⟨Derivation.conjunctionIntroduction t (Derivation.conjunctionIntroduction f₂ a₂)⟩ live cover
  exact ⟨(exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx cod p).mpr ⟨parent,ready⟩,live⟩

#print axioms exact_OpenJoinedAuxiliaryWindow
#print axioms exact_LiteralJoinedAuxiliaryWindow
#print axioms exact_OpenJoinedAuxiliaryParent
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
