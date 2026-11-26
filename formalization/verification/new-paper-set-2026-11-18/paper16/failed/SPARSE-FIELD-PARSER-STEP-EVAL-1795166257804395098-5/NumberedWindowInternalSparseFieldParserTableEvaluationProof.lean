module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open InternalListCodecEvaluationProof (consEvaluation headEvaluation)
open InternalRawListRecursion (lookup)
open InternalRawListRecursionEvaluationProof (lookupConsZero lookupConsSuccessor)
open NumberedWindowInternalSparseFieldParser

theorem tableZero (B : Program 2) (R : Program 4) (ps : List.Vector Nat 2) :
    evaluate (scratchTable B R) (0 ::ᵥ ps) = 1+Nat.pair (evaluate B ps) 0 := by
  change evaluate InternalListCodec.consCode
    (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((![B,InternalAcceptance.constantZero 2] : Fin 2 → Program 2) i) ps) = _
  rw [vectorTwo, consEvaluation]
  rfl

theorem tableSucc (B : Program 2) (R : Program 4) (ps : List.Vector Nat 2) (i : Nat) :
    let old := evaluate (scratchTable B R) (i ::ᵥ ps)
    evaluate (scratchTable B R) ((i+1) ::ᵥ ps) =
      1+Nat.pair (evaluate R (i ::ᵥ old ::ᵥ ps)) old := by
  let old := evaluate (scratchTable B R) (i ::ᵥ ps)
  let args := i ::ᵥ old ::ᵥ ps
  change evaluate InternalListCodec.consCode
    (List.Vector.ofFn fun j : Fin 2 =>
      evaluate ((![R,.projection 1] : Fin 2 → Program 4) j) args) = _
  rw [vectorTwo, consEvaluation]
  rfl

theorem rowValue (B : Program 2) (R : Program 4) (ps : List.Vector Nat 2) (i : Nat) :
    evaluate (scratchRow B R) (i ::ᵥ ps) =
      (Nat.unpair (evaluate (scratchTable B R) (i ::ᵥ ps) - 1)).1 := by
  change evaluate InternalListCodec.headCode (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (scratchTable B R) (i ::ᵥ ps)) = _
  rw [vectorOne, headEvaluation]

theorem rowZero (B : Program 2) (R : Program 4) (ps : List.Vector Nat 2) :
    evaluate (scratchRow B R) (0 ::ᵥ ps) = evaluate B ps := by
  rw [rowValue,tableZero]
  simp [Nat.add_comm 1]

theorem rowSucc (B : Program 2) (R : Program 4) (ps : List.Vector Nat 2) (i : Nat) :
    evaluate (scratchRow B R) ((i+1) ::ᵥ ps) =
      evaluate R (i ::ᵥ evaluate (scratchTable B R) (i ::ᵥ ps) ::ᵥ ps) := by
  rw [rowValue,tableSucc]
  simp [Nat.add_comm 1]

theorem lookupAt (B : Program 2) (R : Program 4) (ps : List.Vector Nat 2)
    (i t : Nat) (hle : t ≤ i) :
    evaluate lookup ((i-t) ::ᵥ evaluate (scratchTable B R) (i ::ᵥ ps) ::ᵥ nil) =
      evaluate (scratchRow B R) (t ::ᵥ ps) := by
  induction i generalizing t with
  | zero =>
    have ht : t = 0 := Nat.eq_zero_of_le_zero hle
    subst t
    rw [tableZero, lookupConsZero, rowZero]
  | succ i ih =>
    by_cases top : t = i+1
    · subst t
      rw [Nat.sub_self, tableSucc, lookupConsZero, rowSucc]
    · have earlier : t ≤ i := by omega
      have offset : i+1-t = (i-t)+1 := by omega
      rw [offset,tableSucc,lookupConsSuccessor]
      exact ih t earlier

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
