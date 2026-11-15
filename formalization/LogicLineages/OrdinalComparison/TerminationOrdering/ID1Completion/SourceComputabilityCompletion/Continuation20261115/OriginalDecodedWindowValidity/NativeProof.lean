module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof NumberedMultisetNumericTotalityProof
open InternalAcceptanceCalibrationProof OriginalRawSyntaxTransportEvaluationSupportProof
open Continuation20261114

theorem stepValue (n head acc : Nat) :
    evaluate (symbolStep n) (head ::ᵥ acc ::ᵥ nil) = if head < n ∧ acc = 1 then 1 else 0 := by
  rw [symbolStep,actualConjunctionEvaluation]
  have hh : evaluate (.composition InternalLessThan.ltTest ![.projection 0,OriginalRawSyntaxTransport.constant 2 n]) (head ::ᵥ acc ::ᵥ nil) =
      if head < n then 1 else 0 := by
    change evaluate InternalLessThan.ltTest (ofFn ![head,evaluate (OriginalRawSyntaxTransport.constant 2 n) (head ::ᵥ acc ::ᵥ nil)]) = _
    rw [constantEvaluation,InternalEqualityTestEvaluationProof.vectorTwo,InternalLessThanEvaluationProof.exactLessThanEvaluation]
    rfl
  rw [hh]
  change (if (if head < n then 1 else 0) = 1 ∧ acc = 1 then 1 else 0) = _
  by_cases h : head < n <;> simp [h]

theorem foldValue (n : Nat) (xs : List Nat) :
    xs.foldr (fun head acc => evaluate (symbolStep n) (head ::ᵥ acc ::ᵥ nil)) 1 =
      (decide (∀ x ∈ xs, x < n)).toNat := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldr_cons,stepValue,ih]
    by_cases h : head < n <;> by_cases ht : ∀ x ∈ tail, x < n <;> simp [h,ht]
    all_goals simp_all

theorem encodedValue (n : Nat) (xs : List Nat) :
    evaluate (symbols n) (numbersNumber xs ::ᵥ nil) = (decide (∀ x ∈ xs, x < n)).toNat := by
  rw [symbols,InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation,numbersRoundTrip]
  change xs.foldr (fun head acc => evaluate (symbolStep n) (head ::ᵥ acc ::ᵥ nil)) 1 = _
  exact foldValue n xs

theorem finListDecode (n : Nat) (xs : List Nat) :
    (Encodable.decode (α := List (Fin n)) (numbersNumber xs)).isSome = decide (∀ x ∈ xs, x < n) := by
  induction xs with
  | nil => simp [numbersNumber]
  | cons head tail ih =>
    have he : numbersNumber (head :: tail) = Nat.succ (Nat.pair head (numbersNumber tail)) := by simp [numbersNumber,Nat.add_comm]
    rw [he,Encodable.decode_list_succ,Nat.unpair_pair,NumberedHeadCodecPrimrecSupportProof.finDecode]
    cases hd : Encodable.decode (α := List (Fin n)) (numbersNumber tail) with
    | none =>
      simp only [hd,Option.isSome_none] at ih
      by_cases h : head < n <;> simp [h,ih.symm] <;> rfl
    | some ys =>
      simp only [hd,Option.isSome_some] at ih
      by_cases h : head < n <;> simp [h,ih.symm] <;> rfl

theorem nativeSymbols : Targets.NativeSymbols := by
  intro n v
  obtain ⟨xs,hx⟩ := encodingSurjective (v.get 0)
  have hv : v = numbersNumber xs ::ᵥ nil := by
    apply List.Vector.ext
    intro i
    exact Fin.cases hx.symm (fun j => Fin.elim0 j) i
  rw [hv,encodedValue]
  exact congrArg Bool.toNat (finListDecode n xs).symm

theorem typeListTotal (raw : Nat) : ∃ xs : List Source.Ty, Encodable.decode raw = some xs := by
  induction raw using Nat.strong_induction_on with
  | h raw ih =>
    cases raw with
    | zero => exact ⟨[],Encodable.decode_list_zero⟩
    | succ k =>
      obtain ⟨xs,hxs⟩ := ih (Nat.unpair k).2 (Nat.lt_succ_of_le (Nat.unpair_right_le k))
      refine ⟨NumberedTypeCodecPrimrec.typeEquiv.symm (Nat.unpair k).1 :: xs, ?_⟩
      rw [Encodable.decode_list_succ,hxs]
      change (some (NumberedTypeCodecPrimrec.typeEquiv.symm (Nat.unpair k).1) |>.map List.cons) <*> some xs = _
      rfl

theorem nativeWindow : Targets.NativeWindow := by
  intro n v
  have he : evaluate (window n) v = evaluate (symbols n) ((Nat.unpair (v.get 0)).1 ::ᵥ nil) := by
    change evaluate (symbols n) (ofFn fun _ : Fin 1 => evaluate InternalUnpair.left v) = _
    rw [InternalEqualityTestEvaluationProof.vectorOne]
    congr 1
    exact congrArg (fun x : Nat => x ::ᵥ nil) (InternalApplicationCertificateConstructorsEvaluationProof.leftEvaluation v)
  rw [he,nativeSymbols,Encodable.decode_prod_val]
  obtain ⟨xs,hxs⟩ := typeListTotal (Nat.unpair (v.get 0)).2
  rw [hxs]
  change (Encodable.decode (α := List (Fin n)) (Nat.unpair (v.get 0)).1).isSome.toNat =
    ((Encodable.decode (α := List (Fin n)) (Nat.unpair (v.get 0)).1).bind
      (fun a => Option.map (Prod.mk a) (some xs))).isSome.toNat
  cases Encodable.decode (α := List (Fin n)) (Nat.unpair (v.get 0)).1 <;> rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.NativeProof
