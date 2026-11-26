module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalRawListRecursionEvaluationProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof NumberedMultisetNumericTotalityProof

theorem constantValue (k : Nat) (v : List.Vector Nat 3) : evaluate (constant k) v = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.succ (evaluate (constant k) v) = k+1
    rw [ih]

theorem dropNil (k : Nat) : evaluate InternalRawListRecursion.drop (k ::ᵥ 0 ::ᵥ nil) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dropSuccessor,ih]; rfl

theorem lookupEncoded (k : Nat) (xs : List Nat) :
    evaluate InternalRawListRecursion.lookup (k ::ᵥ numbersNumber xs ::ᵥ nil) = xs.getD k 0 := by
  induction xs generalizing k with
  | nil => rw [lookupEvaluation,dropNil]; rfl
  | cons head tail ih =>
    cases k with
    | zero => exact lookupConsZero head (numbersNumber tail)
    | succ k =>
      rw [numbersNumber,lookupConsSuccessor,ih,List.getD_cons_succ]

theorem boolGet (k : Nat) (xs : List Nat) :
    (xs.map (fun value => value == 1)).getD k false = (xs.getD k 0 == 1) := by
  induction xs generalizing k with
  | nil => rfl
  | cons head tail ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

theorem nativeSlots : Targets.NativeSlots := by
  intro k v
  obtain ⟨xs,hxs⟩ := decoderTotality (v.get 1)
  have hs := numbersSound (v.get 1) xs hxs
  have hraw : evaluate (rawSlot k) v = xs.getD k 0 := by
    change evaluate InternalRawListRecursion.lookup (ofFn ![evaluate (constant k) v,v.get 1]) = _
    rw [constantValue,← hs,InternalEqualityTestEvaluationProof.vectorTwo]
    exact lookupEncoded k xs
  rw [answer,InternalAcceptanceCalibrationProof.evalNormalize,hraw]
  simp only [hxs,Option.getD_some,boolGet,Bool.beq_eq_decide_eq]
  by_cases h : xs.getD k 0 = 1 <;> simp [h]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
