module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalNormalize evalBranch actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree exactEqualityEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowScalarAlgorithm (Settings admitted vertices)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow packedWindow)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (unaryValue)
open NumberedWindowInternalAuxWindowMemoTargets
  (intrinsicWindow intrinsicType IntrinsicWindowCalibrated selectedIntrinsic)
open NumberedWindowInternalAuxWindowMemoChecks (exact_PackedIntrinsicProjection)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated intrinsicQuery)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseCoverScratchNumericProjectionProof (scratchVerticesValue)
open NumberedWindowInternalSparsePackedLeastNumericTapeProof (contextValue)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalLiteralSyntaxMemoWindow (window)
open NumberedWindowInternalLiteralSyntaxMemoWindowNumericProof (windowStep exact_SyntaxMemoWindow)
open NumberedWindowInternalLiteralCoveredMemo

private theorem ownValue (C : Program 3) (s : Settings) (hC : ActualSelectedCoverOutput C)
    (ctx ty seed : Nat) : evaluate (ownSeed C s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      ((vertices s seed).any (fun head => head == seed)).toNat := by
  let xs := ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil
  have v : evaluate (poolAtSeed C s) xs = numbersNumber (vertices s seed) := by
    rw [poolAtSeed,NumberedWindowInternalSparseOrderedMinimumNumericStepProof.unaryValue]
    exact scratchVerticesValue C hC s seed
  change evaluate scratchMember (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![poolAtSeed C s,.projection 2] : Fin 2 → Program 3) i) xs)) = _
  rw [vectorTwo]
  change evaluate scratchMember (evaluate (poolAtSeed C s) xs ::ᵥ seed ::ᵥ nil) = _
  rw [v,NumberedWindowInternalSparseScratchMembershipNumericChecks.exact_AllInputScratchMembership,numbersRoundTrip]
  rfl

private theorem coverageTrue (C : Program 3) (s : Settings) (cover : ActualSelectedCoverOutput C)
    (seeds : WindowSeedsCovered s) (ctx ty used seed : Nat)
    (held : packedWindow s ctx ty seed = true) :
    evaluate (conjunction contextPresent (ownSeed C s)) (ctx ::ᵥ used ::ᵥ seed ::ᵥ nil) = 1 := by
  obtain ⟨g,parse,accepted⟩ : ∃ g, unpack ctx = some g ∧ admitted s g ty seed = true := by
    cases q : unpack ctx with
    | none => simp [packedWindow,q] at held
    | some g => exact ⟨g,rfl,by simpa [packedWindow,q] using held⟩
  let xs := ctx ::ᵥ used ::ᵥ seed ::ᵥ nil
  have yes : evaluate contextPresent xs = 1 := by
    rw [contextPresent,evalBranch]
    change (if evaluate contextOption (ctx ::ᵥ used ::ᵥ seed ::ᵥ nil) = 0 then _ else _) = _
    rw [contextValue,parse]
    rfl
  have listed : evaluate (ownSeed C s) xs = 1 := by
    rw [ownValue C s cover ctx used seed]
    simp [seeds g ty seed accepted]
  rw [actualConjunctionEvaluation,yes,listed]
  rfl

private theorem coverageValue (C : Program 3) (s : Settings) (i old ctx : Nat) :
    evaluate (coverageAtKey C s) (i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) =
      evaluate (conjunction contextPresent (ownSeed C s)) (ctx ::ᵥ 0 ::ᵥ (i+1) ::ᵥ nil) := by
  let xs := i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil
  unfold coverageAtKey
  rw [evaluate,vectorThree]
  change evaluate (conjunction contextPresent (ownSeed C s))
    (ctx ::ᵥ 0 ::ᵥ evaluate currentKey xs ::ᵥ nil) = _
  have h : evaluate currentKey xs = i+1 := by rw [currentKey,unaryValue]; rfl
  rw [h]

private theorem zeroIntrinsic (s : Settings) (ctx : Nat) : intrinsicWindow s ctx 0 = 0 := by
  have no : (NumberedWindowSyntaxAlgorithm.syntaxBits 0).1 = false := rfl
  cases parse : unpack ctx <;> simp [intrinsicWindow,packedWindow,parse,admitted,typed,no]

theorem coveredStep (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (cover : ActualSelectedCoverOutput C) (seeds : WindowSeedsCovered s)
    (baseFit : IntrinsicWindowCalibrated s base) (typeFit : TypeGuardCalibrated s T)
    (syntaxFit : ActualRawSyntax V) (i old ctx : Nat)
    (previous : ∀ j, j < i+1 → evaluate lookup ((i-j) ::ᵥ old ::ᵥ nil) = intrinsicWindow s ctx j) :
    evaluate (coveredUpdate C s base T V) (i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) =
      intrinsicWindow s ctx (i+1) := by
  let q := i+1
  let t := intrinsicType q
  have updated := windowStep s base T V baseFit typeFit syntaxFit i old ctx previous
  rw [coveredUpdate,evalBranch,evalNormalize,coverageValue]
  by_cases h : evaluate (conjunction contextPresent (ownSeed C s)) (ctx ::ᵥ 0 ::ᵥ q ::ᵥ nil) = 1
  · rw [if_pos h,if_neg (by decide : (1 : Nat) ≠ 0)]
    exact updated
  · rw [if_neg h,if_pos rfl]
    change 0 = intrinsicWindow s ctx q
    unfold intrinsicWindow
    change 0 = if packedWindow s ctx t q then t+1 else 0
    by_cases hp : packedWindow s ctx t q = true
    · exact False.elim (h (coverageTrue C s cover seeds ctx t 0 q hp))
    · have no : packedWindow s ctx t q = false := Bool.eq_false_iff.mpr hp
      rw [no]
      rfl

theorem exact_CoveredMemoIntrinsic (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (cover : ActualSelectedCoverOutput C) (seeds : WindowSeedsCovered s)
    (baseFit : IntrinsicWindowCalibrated s base) (typeFit : TypeGuardCalibrated s T)
    (syntaxFit : ActualRawSyntax V) :
    IntrinsicWindowCalibrated s (coveredIntrinsic C s base T V) := by
  intro ctx n
  unfold coveredIntrinsic
  rw [selectedIntrinsic,compositeThree]
  change evaluate (scratchRow (constantZero 2) (coveredUpdate C s base T V)) (n ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = _
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero,zeroIntrinsic s ctx]; rfl
    | succ i =>
      rw [rowSucc]
      apply coveredStep C s base T V cover seeds baseFit typeFit syntaxFit i _ ctx
      intro j earlier
      rw [lookupAt (constantZero 2) (coveredUpdate C s base T V) (ctx ::ᵥ 0 ::ᵥ nil) i j
        (Nat.le_of_lt_succ earlier)]
      exact ih j earlier

theorem exact_CoveredMemoWindow (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (cover : ActualSelectedCoverOutput C) (seeds : WindowSeedsCovered s)
    (baseFit : IntrinsicWindowCalibrated s base) (typeFit : TypeGuardCalibrated s T)
    (syntaxFit : ActualRawSyntax V) : ActualPackedWindow s (coveredMemoWindow C s base T V) := by
  intro ctx ty raw
  let xs := ctx ::ᵥ ty ::ᵥ raw ::ᵥ nil
  let F := coveredIntrinsic C s base T V
  change evaluate InternalEqualityTest.equalityTest
    (List.Vector.ofFn fun i => evaluate ((![.composition F ![.projection 0,.projection 2],
      .composition .succ ![.projection 1]] : Fin 2 → Program 3) i) xs) = _
  rw [vectorTwo]
  change evaluate InternalEqualityTest.equalityTest
    (evaluate F (List.Vector.ofFn fun i => evaluate ((![.projection 0,.projection 2] : Fin 2 → Program 3) i) xs) ::ᵥ
      evaluate Program.succ (List.Vector.ofFn fun i => evaluate ((![.projection 1] : Fin 1 → Program 3) i) xs) ::ᵥ nil) = _
  rw [vectorTwo,vectorOne]
  change evaluate InternalEqualityTest.equalityTest (evaluate F (ctx ::ᵥ raw ::ᵥ nil) ::ᵥ (ty+1) ::ᵥ nil) = _
  rw [exact_CoveredMemoIntrinsic C s base T V cover seeds baseFit typeFit syntaxFit,exactEqualityEvaluation,
    exact_PackedIntrinsicProjection]
  split
  · rename_i eq
    simp [eq]
  · rename_i ne
    have no : (intrinsicWindow s ctx raw == ty+1) = false := Bool.eq_false_iff.mpr (fun h => ne (beq_iff_eq.mp h))
    simp [no]

#print axioms exact_CoveredMemoIntrinsic
#print axioms exact_CoveredMemoWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoNumericProof
