module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicCoveredCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDualTypedRawProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration packedRaw)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm)
open NumberedWindowInternalLiteralAtomicTypedGuardReturnProof (RawAtoms)
open NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof
  (auxiliaryAtomicTypedRaw exact_OpenLiteralAuxiliaryAtomicRawAtoms)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot atomicFallback)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Retain the full original covered raw graph and one more actual
typed endpoint query. Both use a literally identical own-run and
syntax program. Only the two window ASTs are distinct. -/
def dualTypedRaw (p other A Z : Program 3) (V : Program 1) : Program 5 :=
  conjunction (auxiliaryAtomicTypedRaw p other A V) (auxiliaryAtomicTypedRaw p other Z V)

theorem exact_LiteralDualRawCalibration (xs : Entries) (s : Settings) (p other A Z : Program 3) (V : Program 1)
    (old : ActualRawCalibration xs s (auxiliaryAtomicTypedRaw p other A V))
    (new : ActualRawCalibration xs s (auxiliaryAtomicTypedRaw p other Z V)) :
    ActualRawCalibration xs s (dualTypedRaw p other A Z V) := by
  intro ctx ty q w r
  rw [dualTypedRaw,actualConjunctionEvaluation,old ctx ty q w r,new ctx ty q w r]
  cases b : packedRaw xs s ctx ty q w r <;> rfl

private abbrev probes (p other A : Program 3) (V : Program 1) (ctx ty q w r : OTerm α) :=
  exact_OpenTypedRaw5 B (atomicRoot p) (auxiliaryFallback (atomicFallback other)) A V α Γ ctx ty q w r

theorem exact_OpenDualTypedRawEndpoints (p other A Z : Program 3) (V : Program 1)
    (ctx ty q w r : OTerm α)
    (held : D B Γ (programGraph (dualTypedRaw p other A Z V) (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph (auxiliaryAtomicTypedRaw p other A V) (suc z) ![ctx,ty,q,w,r] ⊓
      (windowAt Z ctx ty q ⊓ windowAt Z ctx ty r)) := by
  obtain ⟨both⟩ := conjunctionRecover (auxiliaryAtomicTypedRaw p other A V)
    (auxiliaryAtomicTypedRaw p other Z V) ![ctx,ty,q,w,r] held
  obtain ⟨iff⟩ := probes (B := B) (Γ := Γ) p other Z V ctx ty q w r
  let payload := Derivation.implicationElimination (Derivation.conjunctionLeft iff)
    (Derivation.conjunctionRight both)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft both) (Derivation.conjunctionRight payload)⟩

/-- Rebuild the second physical checker from the literal SAME original
run and both actual new window reports, so a contextual child can
reconstruct the exact combined raw callback. -/
theorem exact_OpenDualTypedRawIntro (p other A Z : Program 3) (V : Program 1)
    (ctx ty q w r : OTerm α)
    (left : D B Γ (programGraph (auxiliaryAtomicTypedRaw p other A V) (suc z) ![ctx,ty,q,w,r]))
    (src : D B Γ (windowAt Z ctx ty q)) (dst : D B Γ (windowAt Z ctx ty r)) :
    D B Γ (programGraph (dualTypedRaw p other A Z V) (suc z) ![ctx,ty,q,w,r]) := by
  obtain ⟨iffA⟩ := probes (B := B) (Γ := Γ) p other A V ctx ty q w r
  obtain ⟨iffZ⟩ := probes (B := B) (Γ := Γ) p other Z V ctx ty q w r
  obtain ⟨d⟩ := left
  obtain ⟨s⟩ := src
  obtain ⟨t⟩ := dst
  have old := Derivation.implicationElimination (Derivation.conjunctionLeft iffA) d
  have new := Derivation.implicationElimination (Derivation.conjunctionRight iffZ)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft old) (Derivation.conjunctionIntroduction s t))
  exact conjunctionAccept (auxiliaryAtomicTypedRaw p other A V) (auxiliaryAtomicTypedRaw p other Z V)
    ![ctx,ty,q,w,r] ⟨d⟩ ⟨new⟩

theorem exact_OpenDualTypedRawAtoms (p other A Z : Program 3) (V : Program 1) :
    RawAtoms (dualTypedRaw p other A Z V) := by
  let atoms := exact_OpenLiteralAuxiliaryAtomicRawAtoms p other A V
  constructor
  · intro B α Γ ctx ty t n w r held
    obtain ⟨old⟩ := exact_OpenDualTypedRawEndpoints p other A Z V ctx ty (freeTerm t n) w r held
    exact atoms.free B α Γ ctx ty t n w r ⟨Derivation.conjunctionLeft old⟩
  · intro B α Γ ctx ty t w r held
    obtain ⟨old⟩ := exact_OpenDualTypedRawEndpoints p other A Z V ctx ty (bottomTerm t) w r held
    exact atoms.bottom B α Γ ctx ty t w r ⟨Derivation.conjunctionLeft old⟩

#print axioms exact_LiteralDualRawCalibration
#print axioms exact_OpenDualTypedRawEndpoints
#print axioms exact_OpenDualTypedRawIntro
#print axioms exact_OpenDualTypedRawAtoms
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDualTypedRawProof
