module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationRepeatProof
open OriginalHereditaryLambda OriginalHereditaryLambdaRawProof
open InternalRawListRepeat InternalRawListRecursionEvaluationProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof NumberedMultisetNumericTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev repeatValue (transition : Program 1) (code state : Nat) : Nat :=
  evaluate (repeatProgram transition) (List.Vector.ofFn ![code,state])

theorem repeatStepEvaluation (transition : Program 1) (head state initial : Nat) :
    evaluate (repeatStep transition) (head ::ᵥ state ::ᵥ initial ::ᵥ List.Vector.nil) =
      evaluate transition (List.Vector.ofFn ![state]) := by
  change evaluate transition (List.Vector.ofFn fun _ : Fin 1 => state) = _
  simp only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero]

theorem repeatEvaluation (transition : Program 1) (code state : Nat) :
    repeatValue transition code state =
      ((decodeNumbers code).getD []).foldr
        (fun _ result => evaluate transition (List.Vector.ofFn ![result])) state := by
  unfold repeatValue
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  change evaluate (InternalRawListRecursion.listRec (Program.projection (0 : Fin 1))
    (repeatStep transition)) (code ::ᵥ state ::ᵥ List.Vector.nil) = _
  rw [actualRawListRecursionEvaluation]
  simp only [repeatStepEvaluation]
  rfl

theorem repeatZero (transition : Program 1) (state : Nat) :
    repeatValue transition 0 state = state := by
  rw [repeatEvaluation]
  rfl

theorem repeatCons (transition : Program 1) (head tail state : Nat) :
    repeatValue transition (1 + Nat.pair head tail) state =
      evaluate transition (List.Vector.ofFn ![repeatValue transition tail state]) := by
  obtain ⟨xs,hxs⟩ := decoderTotality tail
  have he := numbersSound tail xs hxs
  have hc : decodeNumbers (1 + Nat.pair head tail) = some (head :: xs) := by
    rw [← he]
    exact numbersRoundTrip (head :: xs)
  rw [repeatEvaluation,repeatEvaluation,hc,hxs]
  rfl

theorem foldTransition (transition : Program 1) (xs : List Nat) (state : Nat) :
    xs.foldr (fun _ result => evaluate transition (List.Vector.ofFn ![result]))
        (evaluate transition (List.Vector.ofFn ![state])) =
      evaluate transition (List.Vector.ofFn
        ![xs.foldr (fun _ result => evaluate transition (List.Vector.ofFn ![result])) state]) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldr_cons]
    rw [ih]

theorem repeatFrontCons (transition : Program 1) (head tail state : Nat) :
    repeatValue transition (1 + Nat.pair head tail) state =
      repeatValue transition tail (evaluate transition (List.Vector.ofFn ![state])) := by
  rw [repeatCons,repeatEvaluation,repeatEvaluation]
  exact (foldTransition transition ((decodeNumbers tail).getD []) state).symm

theorem repeatFixed (transition : Program 1) (code state : Nat)
    (h : evaluate transition (List.Vector.ofFn ![state]) = state) :
    repeatValue transition code state = state := by
  rw [repeatEvaluation]
  have hf : ∀ xs : List Nat,
      xs.foldr (fun _ result => evaluate transition (List.Vector.ofFn ![result])) state = state := by
    intro xs
    induction xs with
    | nil => rfl
    | cons head tail ih => simpa only [List.foldr_cons,ih] using h
  exact hf _

theorem runEvaluation (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (run oldStep) v =
      repeatValue (transition oldStep) (Nat.unpair (v.get 2)).1 (liveValue v) := by
  change evaluate (repeatProgram (transition oldStep))
    (List.Vector.ofFn fun i : Fin 2 => evaluate ((![path,live] : Fin 2 → Program 4) i) v) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  change evaluate (repeatProgram (transition oldStep))
    (evaluate path v ::ᵥ evaluate live v ::ᵥ List.Vector.nil) = _
  rw [pathEvaluation,liveEvaluation]
  rfl

theorem guardEvaluation (oldStep : Program 4) (v : List.Vector Nat 4) :
    evaluate (guard oldStep) v =
      evaluate finish (List.Vector.ofFn
        ![repeatValue (transition oldStep) (Nat.unpair (v.get 2)).1 (liveValue v)]) := by
  change evaluate finish (List.Vector.ofFn fun _ : Fin 1 => evaluate (run oldStep) v) = _
  rw [runEvaluation]
  simp only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationRepeatProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationRepeatProof
