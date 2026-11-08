module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalRawListRecursion InternalListCodec InternalListCodecEvaluationProof
open InternalEqualityTestEvaluationProof InternalUnpairEvaluationProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof NumberedMultisetNumericTotalityProof

attribute [local irreducible] consCode headCode tailCode InternalEqualityTest.subtract

theorem vectorTwo (f : Fin 2 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ List.Vector.nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)) i <;> simp

theorem dropZero (code : Nat) :
    evaluate drop (0 ::ᵥ code ::ᵥ List.Vector.nil) = code := rfl

theorem dropSuccessor (index code : Nat) :
    evaluate drop ((index+1) ::ᵥ code ::ᵥ List.Vector.nil) =
      (Nat.unpair (evaluate drop (index ::ᵥ code ::ᵥ List.Vector.nil) - 1)).2 := by
  change evaluate tailCode (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate drop (index ::ᵥ code ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,tailEvaluation]

theorem dropCons (index head tail : Nat) :
    evaluate drop ((index+1) ::ᵥ (1 + Nat.pair head tail) ::ᵥ List.Vector.nil) =
      evaluate drop (index ::ᵥ tail ::ᵥ List.Vector.nil) := by
  induction index with
  | zero => simp only [dropSuccessor,dropZero]; simp [Nat.add_comm 1]
  | succ index ih => rw [dropSuccessor,ih,dropSuccessor]

theorem lookupEvaluation (index code : Nat) :
    evaluate lookup (index ::ᵥ code ::ᵥ List.Vector.nil) =
      (Nat.unpair (evaluate drop (index ::ᵥ code ::ᵥ List.Vector.nil) - 1)).1 := by
  change evaluate headCode (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate drop (index ::ᵥ code ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,headEvaluation]

theorem lookupConsZero (head tail : Nat) :
    evaluate lookup (0 ::ᵥ (1 + Nat.pair head tail) ::ᵥ List.Vector.nil) = head := by
  rw [lookupEvaluation,dropZero]
  simp [Nat.add_comm 1]

theorem lookupConsSuccessor (index head tail : Nat) :
    evaluate lookup ((index+1) ::ᵥ (1 + Nat.pair head tail) ::ᵥ List.Vector.nil) =
      evaluate lookup (index ::ᵥ tail ::ᵥ List.Vector.nil) := by
  rw [lookupEvaluation,dropCons,lookupEvaluation]

theorem tableZero {k : Nat} (base : Program k) (step : Program (k+2))
    (params : List.Vector Nat k) :
    evaluate (table base step) (0 ::ᵥ params) = 1 + Nat.pair (evaluate base params) 0 := by
  change evaluate consCode (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons base (Fin.cons zero Fin.elim0) : Fin 2 → Program k) i) params) = _
  rw [vectorTwo,consEvaluation]
  rfl

theorem tableSuccessor {k : Nat} (base : Program k) (step : Program (k+2))
    (params : List.Vector Nat k) (index : Nat) :
    evaluate (table base step) ((index+1) ::ᵥ params) =
      1 + Nat.pair
        (evaluate step ((Nat.unpair index).1 ::ᵥ
          evaluate lookup ((index - (Nat.unpair index).2) ::ᵥ
            evaluate (table base step) (index ::ᵥ params) ::ᵥ List.Vector.nil) ::ᵥ params))
        (evaluate (table base step) (index ::ᵥ params)) := by
  let previous := evaluate (table base step) (index ::ᵥ params)
  let inputs := index ::ᵥ previous ::ᵥ params
  have hh : evaluate (nextHead : Program (k+2)) inputs = (Nat.unpair index).1 := by
    change evaluate headCode (List.Vector.ofFn fun _ : Fin 1 => index+1) = _
    rw [vectorOne,headEvaluation]
    simp
  have ht : evaluate (nextTail : Program (k+2)) inputs = (Nat.unpair index).2 := by
    change evaluate tailCode (List.Vector.ofFn fun _ : Fin 1 => index+1) = _
    rw [vectorOne,tailEvaluation]
    simp
  have hi : evaluate (previousIndex : Program (k+2)) inputs = index - (Nat.unpair index).2 := by
    change evaluate InternalEqualityTest.subtract (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((Fin.cons nextTail
        (Fin.cons (Program.projection 0) Fin.elim0) : Fin 2 → Program (k+2)) i) inputs) = _
    rw [vectorTwo]
    change evaluate InternalEqualityTest.subtract
      (evaluate (nextTail : Program (k+2)) inputs ::ᵥ index ::ᵥ List.Vector.nil) = _
    rw [ht,exactSubtractionEvaluation]
  have hv : evaluate (previousValue : Program (k+2)) inputs =
      evaluate lookup ((index - (Nat.unpair index).2) ::ᵥ previous ::ᵥ List.Vector.nil) := by
    change evaluate lookup (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((Fin.cons previousIndex
        (Fin.cons (Program.projection 1) Fin.elim0) : Fin 2 → Program (k+2)) i) inputs) = _
    rw [vectorTwo]
    change evaluate lookup
      (evaluate (previousIndex : Program (k+2)) inputs ::ᵥ previous ::ᵥ List.Vector.nil) = _
    rw [hi]
  have hn : evaluate (nextValue step) inputs =
      evaluate step ((Nat.unpair index).1 ::ᵥ
        evaluate lookup ((index - (Nat.unpair index).2) ::ᵥ previous ::ᵥ List.Vector.nil) ::ᵥ params) := by
    change evaluate step (List.Vector.ofFn fun i =>
      evaluate ((Fin.cons nextHead (Fin.cons previousValue
        (fun i => Program.projection i.succ.succ)) : Fin (k+2) → Program (k+2)) i) inputs) = _
    congr 1
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun q => ?_)) i
    · exact hh
    · exact hv
    · simp [inputs,evaluate]
  change evaluate consCode (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons (nextValue step) (Fin.cons (Program.projection 1) Fin.elim0) :
      Fin 2 → Program (k+2)) i) inputs) = _
  rw [vectorTwo,consEvaluation]
  change 1 + Nat.pair (evaluate (nextValue step) inputs) previous = _
  rw [hn]

def foldedValue {k : Nat} (base : Program k) (step : Program (k+2))
    (params : List.Vector Nat k) (code : Nat) : Nat :=
  ((decodeNumbers code).getD []).foldr
    (fun head result => evaluate step (head ::ᵥ result ::ᵥ params)) (evaluate base params)

theorem foldedZero {k : Nat} (base : Program k) (step : Program (k+2))
    (params : List.Vector Nat k) : foldedValue base step params 0 = evaluate base params := rfl

theorem foldedSuccessor {k : Nat} (base : Program k) (step : Program (k+2))
    (params : List.Vector Nat k) (index : Nat) :
    foldedValue base step params (index+1) =
      evaluate step ((Nat.unpair index).1 ::ᵥ
        foldedValue base step params (Nat.unpair index).2 ::ᵥ params) := by
  obtain ⟨xs,hxs⟩ := decoderTotality (Nat.unpair index).2
  have he := numbersSound _ _ hxs
  have hn : numbersNumber ((Nat.unpair index).1 :: xs) = index+1 := by
    simp only [numbersNumber,he,Nat.pair_unpair]
    omega
  unfold foldedValue
  rw [← hn,numbersRoundTrip,hxs]
  rfl

/-- The table entry for every earlier raw code computes its literal decoded
list fold. The induction uses the actual unpair tail bound, without a validity
or successful-decoding hypothesis on the caller's code. -/
theorem tableLookup {k : Nat} (base : Program k) (step : Program (k+2))
    (params : List.Vector Nat k) (index code : Nat) (h : code ≤ index) :
    evaluate lookup ((index-code) ::ᵥ evaluate (table base step) (index ::ᵥ params) ::ᵥ List.Vector.nil) =
      foldedValue base step params code := by
  induction index generalizing code with
  | zero =>
    have hz : code=0 := by omega
    subst code
    rw [tableZero]
    exact lookupConsZero _ _
  | succ index ih =>
    rw [tableSuccessor]
    by_cases he : code=index+1
    · subst code
      rw [Nat.sub_self,lookupConsZero,ih _ (Nat.unpair_right_le index),foldedSuccessor]
    · have hc : code ≤ index := by omega
      have hd : index+1-code = (index-code)+1 := by omega
      rw [hd,lookupConsSuccessor]
      exact ih code hc

theorem actualRawListRecursionEvaluation :
    InternalRawListRecursionTargets.ActualRawListRecursionEvaluation := by
  intro k base step params code
  have h := tableLookup base step params code code (Nat.le_refl code)
  rw [Nat.sub_self,lookupEvaluation,dropZero] at h
  change evaluate headCode (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (table base step) (code ::ᵥ params)) = _
  rw [vectorOne,headEvaluation]
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
