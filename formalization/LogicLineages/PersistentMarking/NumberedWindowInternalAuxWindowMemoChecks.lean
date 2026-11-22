module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalRawListRecursion (lookup)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowAnnotationAlgorithm (annotations arrow termNext termParts)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowAuxExchangeLiftChecks (exact_AuxWindowAdmission)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalAuxWindowMemoTargets

private theorem ownAnnotationFactor (s : Settings) (g : List Nat) (ty raw : Nat) :
    admitted s g ty raw = ((intrinsicType raw == ty) && admitted s g (intrinsicType raw) raw) := by
  simp [admitted,typed,intrinsicType,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

private theorem packedFactor (s : Settings) (ctx ty raw : Nat) :
    packedWindow s ctx ty raw = ((intrinsicType raw == ty) && packedWindow s ctx (intrinsicType raw) raw) := by
  cases dec : unpack ctx with
  | none => simp [packedWindow,dec]
  | some g => simpa only [packedWindow,dec,Option.any_some] using ownAnnotationFactor s g ty raw

theorem exact_PackedIntrinsicProjection : ExactPackedIntrinsicProjection := by
  intro s ctx ty raw
  rw [packedFactor]
  cases valid : packedWindow s ctx (intrinsicType raw) raw <;>
    simp [intrinsicWindow,valid]

private theorem annotationAux (dom cod fn arg : Nat) : intrinsicType (auxRaw dom cod fn arg) = cod := by
  simp [intrinsicType,annotations,termNext,termParts,auxView]

private theorem packedAux (s : Settings) (ctx dom cod fn arg : Nat) :
    packedWindow s ctx cod (auxRaw dom cod fn arg) =
      (typeGuard s dom && typeGuard s cod && packedWindow s ctx (arrow dom cod) fn && packedWindow s ctx dom arg) := by
  cases dec : unpack ctx with
  | none => simp [packedWindow,dec]
  | some g =>
    simp only [packedWindow,dec,Option.any_some]
    rw [exact_AuxWindowAdmission s g dom cod fn arg]
    simp [-List.contains_eq_mem,typeGuard,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

theorem exact_IntrinsicAuxWindow : ExactIntrinsicAuxWindow := by
  intro s ctx dom cod fn arg
  rw [← exact_PackedIntrinsicProjection s ctx (arrow dom cod) fn,← exact_PackedIntrinsicProjection s ctx dom arg]
  rw [intrinsicWindow,annotationAux,packedAux]

private theorem rawZero (s : Settings) (ctx : Nat) : intrinsicWindow s ctx 0 = 0 := by
  have noSyntax : (syntaxBits 0).1 = false := rfl
  cases dec : unpack ctx <;> simp [intrinsicWindow,packedWindow,dec,admitted,typed,noSyntax]

private theorem stepCorrect (s : Settings) (base : Program 2) (cal : IntrinsicWindowCalibrated s base)
    (i old ctx : Nat) (prior : ∀ n, n < i+1 →
      evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = intrinsicWindow s ctx n) :
    rowValue s base i old ctx = intrinsicWindow s ctx (i+1) := by
  unfold rowValue
  split
  next dom cod fn arg read =>
    split
    next active =>
      obtain ⟨fnSmall,argSmall,domAllowed,codAllowed,fnReport,argReport⟩ := active
      rw [prior fn fnSmall] at fnReport
      rw [prior arg argSmall] at argReport
      rw [codeOfNode read]
      change cod+1 = intrinsicWindow s ctx (auxRaw dom cod fn arg)
      rw [exact_IntrinsicAuxWindow s ctx dom cod fn arg]
      simp [domAllowed,codAllowed,fnReport,argReport]
    next => exact cal ctx (i+1)
  next => exact cal ctx (i+1)

private theorem tableCorrect (s : Settings) (base : Program 2) (R : Program 4)
    (cal : IntrinsicWindowCalibrated s base) (step : WindowStepCalibrated s base R) (ctx n : Nat) :
    evaluate (scratchRow (constantZero 2) R) (n ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = intrinsicWindow s ctx n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero,rawZero] <;> rfl
    | succ i =>
      rw [rowSucc,step]
      apply stepCorrect s base cal
      intro child earlier
      rw [lookupAt (constantZero 2) R (ctx ::ᵥ 0 ::ᵥ nil) i child (Nat.le_of_lt_succ earlier)]
      exact ih child earlier

theorem exact_IntrinsicMemoCalibration : ExactIntrinsicMemoCalibration := by
  intro s base R cal step ctx raw
  rw [selectedIntrinsic,compositeThree]
  exact tableCorrect s base R cal step ctx raw

#print axioms exact_PackedIntrinsicProjection
#print axioms exact_IntrinsicAuxWindow
#print axioms exact_IntrinsicMemoCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
