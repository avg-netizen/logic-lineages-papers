module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparsePathAdvanceTargets (packedRaw ActualRawCalibration)
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt literal compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (literalEvaluation zeroEvaluation compositeTwo compareEvaluation)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (firstField)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (pack packNode unpack unpackNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowAtomicRawStepFieldProof (nodePacked codeOfNode)
open NumberedWindowAtomicRawStepChecks (exact_ConcreteAtomicRawStep)

def freeTest : Program 1 := nodeGood (literal 1 0) 2
def bottomTest : Program 1 := nodeGood (literal 1 3) 1

def atRawSource (p : Program 1) : Program 5 :=
  .composition p (fun _ : Fin 1 => .projection 2)

def emitRawBottom : Program 1 :=
  consOf (literal 1 3) (consOf (field 0) (zeroAt 1))

def exactRawBottom : Program 5 := .composition compareNumbers
  (Fin.cons (.projection 4) (Fin.cons (atRawSource emitRawBottom) Fin.elim0))

/-- A selectable wrapper of the original raw five-input program, not
of the positive address checker or of an external relation. Its new
branches touch neither the packed context/type nor the raw witness.
It is only a choice of AST; installed presentations must be rebuilt
on this exact wrapper rather than identified by its numeric fit. -/
def guardedRaw (raw : Program 5) : Program 5 :=
  branch (atRawSource freeTest)
    (branch (atRawSource bottomTest) raw (constantZero 5))
    (conjunction raw exactRawBottom)

private theorem unpackedShape (tag arity q : Nat) :
    run (nodeGood (literal 1 tag) arity) q = 1 ↔
      ∃ fields, unpackNode q = some (tag,fields) ∧ fields.length = arity :=
  nodeArity (literal 1 tag) arity q tag (literalEvaluation 1 tag (q ::ᵥ nil))

private theorem nodeBit (tag arity q : Nat) :
    run (nodeGood (literal 1 tag) arity) q = 0 ∨ run (nodeGood (literal 1 tag) arity) q = 1 := by
  unfold run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

theorem freeCode (q : Nat) : run freeTest q = 1 ↔ ∃ t n, q = freeRaw t n := by
  rw [freeTest,unpackedShape]
  constructor
  · rintro ⟨fields,report,len⟩
    rcases fields with _ | ⟨t,_ | ⟨n,_ | ⟨x,xs⟩⟩⟩ <;> simp at len
    exact ⟨t,n,codeOfNode report⟩
  · rintro ⟨t,n,rfl⟩
    exact ⟨[t,n],nodePacked 0 [t,n],rfl⟩

theorem bottomCode (q : Nat) : run bottomTest q = 1 ↔ ∃ t, q = bottomRaw t := by
  rw [bottomTest,unpackedShape]
  constructor
  · rintro ⟨fields,report,len⟩
    rcases fields with _ | ⟨t,_ | ⟨x,xs⟩⟩ <;> simp at len
    exact ⟨t,codeOfNode report⟩
  · rintro ⟨t,rfl⟩
    exact ⟨[t],nodePacked 3 [t],rfl⟩

abbrev args (ctx ty q w r : Nat) : List.Vector Nat 5 := ctx ::ᵥ ty ::ᵥ q ::ᵥ w ::ᵥ r ::ᵥ nil

theorem sourceValue (p : Program 1) (ctx ty q w r : Nat) :
    evaluate (atRawSource p) (args ctx ty q w r) = run p q := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (.projection (2 : Fin 5)) (args ctx ty q w r)) = _
  rw [vectorOne]
  rfl

private theorem consValue (p q : Program 1) (x : Nat) :
    run (consOf p q) x = pair (run p x) (run q x) + 1 := by
  unfold run
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

theorem bottomAtRaw (tag t : Nat) (tail : List Nat) :
    run emitRawBottom (packNode tag (t::tail)) = bottomRaw t := by
  have literal3 : run (literal 1 3) (packNode tag (t::tail)) = 3 :=
    literalEvaluation 1 3 _
  have zero : run (zeroAt 1) (packNode tag (t::tail)) = 0 := zeroEvaluation _
  rw [emitRawBottom,consValue,consValue,literal3,firstField,zero]
  rfl

theorem rawTargetEvaluation (ctx ty tag t : Nat) (tail : List Nat) (w r : Nat) :
    evaluate exactRawBottom (args ctx ty (packNode tag (t::tail)) w r) =
      if r = bottomRaw t then 1 else 0 := by
  rw [exactRawBottom,compositeTwo,sourceValue,bottomAtRaw]
  exact compareEvaluation r (bottomRaw t)

theorem packedFreeResult (xs : Entries) (s : Settings) (ctx ty t n w r : Nat)
    (h : packedRaw xs s ctx ty (freeRaw t n) w r = true) : r = bottomRaw t := by
  unfold packedRaw at h
  cases hc : unpack ctx with
  | none => simp [hc] at h
  | some g =>
    have ok : NumberedWindowConcreteCheckers.step xs s g ty (freeRaw t n) w r = true := by
      simpa only [hc,Option.any_some] using h
    exact (exact_ConcreteAtomicRawStep.1 xs s g ty t n w r ok).1

theorem packedBottomReject (xs : Entries) (s : Settings) (ctx ty t w r : Nat) :
    packedRaw xs s ctx ty (bottomRaw t) w r = false := by
  unfold packedRaw
  cases hc : unpack ctx with
  | none => rfl
  | some g => exact exact_ConcreteAtomicRawStep.2 xs s g ty t w r

/-- Calibrate the actual atom-aware raw AST at every input, including
malformed addresses, contexts, certificates and destinations. Later
ordinary proof rules may exploit this AST only after physical selection. -/
theorem exact_LiteralAtomicGuardedRaw (xs : Entries) (s : Settings) (raw : Program 5)
    (cal : ActualRawCalibration xs s raw) : ActualRawCalibration xs s (guardedRaw raw) := by
  intro ctx ty q w r
  change evaluate (guardedRaw raw) (args ctx ty q w r) = _
  rw [guardedRaw,evalBranch,sourceValue]
  rcases nodeBit 0 2 q with free0 | free1
  · rw [show run freeTest q = 0 from free0,if_pos rfl,evalBranch,sourceValue]
    rcases nodeBit 3 1 q with bot0 | bot1
    · rw [show run bottomTest q = 0 from bot0,if_pos rfl]
      exact cal ctx ty q w r
    · obtain ⟨t,rfl⟩ := (bottomCode q).mp bot1
      rw [show run bottomTest (bottomRaw t) = 1 from bot1,if_neg (by decide : (1 : Nat) ≠ 0)]
      rw [packedBottomReject]
      rfl
  · rw [show run freeTest q = 1 from free1,if_neg (by decide : (1 : Nat) ≠ 0),conjunctionEvaluation]
    by_cases h : packedRaw xs s ctx ty q w r = true
    · obtain ⟨t,n,rfl⟩ := (freeCode q).mp free1
      have e := packedFreeResult xs s ctx ty t n w r h
      change (if evaluate raw (args ctx ty (freeRaw t n) w r) = 1 ∧
        evaluate exactRawBottom (args ctx ty (freeRaw t n) w r) = 1 then 1 else 0) = _
      rw [cal ctx ty (freeRaw t n) w r,if_pos h]
      have b : evaluate exactRawBottom (args ctx ty (freeRaw t n) w r) = 1 := by
        have selected := rawTargetEvaluation ctx ty 0 t [n] w r
        rw [if_pos e] at selected
        exact selected
      simp [b]
    · rw [cal ctx ty q w r,if_neg h]
      simp

#print axioms exact_LiteralAtomicGuardedRaw
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardProof
