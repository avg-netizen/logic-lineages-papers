module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalNormalize evalBranch)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow packedWindow)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (unaryValue)
open NumberedWindowInternalAuxWindowMemoTargets
  (intrinsicWindow intrinsicType IntrinsicWindowCalibrated selectedIntrinsic)
open NumberedWindowInternalAuxWindowMemoChecks (exact_PackedIntrinsicProjection)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated intrinsicQuery)
open NumberedWindowInternalStrictAuxWindowNumericProof (exact_StrictAuxWindowStepCalibration)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalLiteralSyntaxMemoWindow

private theorem noWindow (s : Settings) (ctx raw : Nat) (falseSyntax : (syntaxBits raw).1 = false) :
    intrinsicWindow s ctx raw = 0 := by
  cases seen : unpack ctx <;> simp [intrinsicWindow,packedWindow,seen,admitted,typed,falseSyntax]

theorem windowStep (s : Settings) (base : Program 2) (T V : Program 1)
    (baseFit : IntrinsicWindowCalibrated s base) (typeFit : TypeGuardCalibrated s T)
    (syntaxFit : ActualRawSyntax V) (i old ctx : Nat)
    (previous : ∀ j, j < i+1 → evaluate lookup ((i-j) ::ᵥ old ::ᵥ nil) = intrinsicWindow s ctx j) :
    evaluate (update base T V) (i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = intrinsicWindow s ctx (i+1) := by
  have key : evaluate currentKey (i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = i+1 := by
    rw [currentKey,unaryValue]
    rfl
  have fit : NumberedWindowInternalSparsePathEnvelope.run V (i+1) = (syntaxBits (i+1)).1.toNat := syntaxFit (i+1)
  rw [update,evalBranch,evalNormalize,syntaxAtKey,unaryValue,key,fit]
  cases yes : (syntaxBits (i+1)).1
  · rw [noWindow s ctx (i+1) yes]
    rfl
  · exact exact_StrictAuxWindowStepCalibration s base T baseFit typeFit i old ctx previous

theorem exact_SyntaxMemoIntrinsic (s : Settings) (base : Program 2) (T V : Program 1)
    (baseFit : IntrinsicWindowCalibrated s base) (typeFit : TypeGuardCalibrated s T)
    (syntaxFit : ActualRawSyntax V) : IntrinsicWindowCalibrated s (intrinsic base T V) := by
  intro ctx n
  unfold intrinsic
  rw [selectedIntrinsic,compositeThree]
  change evaluate (scratchRow (constantZero 2) (update base T V)) (n ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = _
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [rowZero,noWindow s ctx 0 rfl]
      rfl
    | succ i =>
      rw [rowSucc]
      apply windowStep s base T V baseFit typeFit syntaxFit i _ ctx
      intro j earlier
      rw [lookupAt (constantZero 2) (update base T V) (ctx ::ᵥ 0 ::ᵥ nil) i j (Nat.le_of_lt_succ earlier)]
      exact ih j earlier

theorem exact_SyntaxMemoWindow (s : Settings) (base : Program 2) (T V : Program 1)
    (baseFit : IntrinsicWindowCalibrated s base) (typeFit : TypeGuardCalibrated s T)
    (syntaxFit : ActualRawSyntax V) : ActualPackedWindow s (window base T V) := by
  intro ctx ty raw
  let xs := ctx ::ᵥ ty ::ᵥ raw ::ᵥ nil
  let F := intrinsic base T V
  change evaluate InternalEqualityTest.equalityTest
    (List.Vector.ofFn fun i => evaluate ((![.composition F ![.projection 0,.projection 2],
      .composition .succ ![.projection 1]] : Fin 2 → Program 3) i) xs) = _
  rw [vectorTwo]
  change evaluate InternalEqualityTest.equalityTest
    (evaluate F (List.Vector.ofFn fun i => evaluate ((![.projection 0,.projection 2] : Fin 2 → Program 3) i) xs) ::ᵥ
      evaluate Program.succ (List.Vector.ofFn fun i => evaluate ((![.projection 1] : Fin 1 → Program 3) i) xs) ::ᵥ nil) = _
  rw [vectorTwo,vectorOne]
  change evaluate InternalEqualityTest.equalityTest (evaluate F (ctx ::ᵥ raw ::ᵥ nil) ::ᵥ (ty+1) ::ᵥ nil) = _
  rw [exact_SyntaxMemoIntrinsic s base T V baseFit typeFit syntaxFit,exactEqualityEvaluation,
    exact_PackedIntrinsicProjection]
  split
  · rename_i same
    simp [same]
  · rename_i unequal
    have none : (intrinsicWindow s ctx raw == ty+1) = false := Bool.eq_false_iff.mpr (fun h => unequal (beq_iff_eq.mp h))
    simp [none]

#print axioms exact_SyntaxMemoIntrinsic
#print axioms exact_SyntaxMemoWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowNumericProof
