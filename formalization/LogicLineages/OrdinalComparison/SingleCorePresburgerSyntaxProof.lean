module
public import LogicLineages.OrdinalComparison.SingleCoreBoxProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger

def tailFormula (support : List Nat) (N : Nat) : SingleCorePresburgerExpr :=
  support.foldr (fun i rest => .disj (.lower i N) rest) (.truth false)

def pointFormula (support word : List Nat) : SingleCorePresburgerExpr :=
  (List.range support.length).foldr
    (fun i rest => .conj (.equal (support.getD i 0) (word.getD i 1)) rest) (.truth true)

noncomputable def boxFormula (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat)
    (support : List Nat) (words : List (List Nat)) : SingleCorePresburgerExpr :=
  words.foldr (fun word rest => if encodedSingleCoreBoxSign source row word=desired then
    .disj (pointFormula support word) rest else rest) (.truth false)

noncomputable def compiledFormula (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat) : SingleCorePresburgerExpr :=
  let support := encodedSingleCoreSupport source
  let result := encodedSingleCoreRowSign row
  .disj (.conj (tailFormula support result.2) (.truth (decide (result.1=desired))))
    (boxFormula source row desired support (singleCoreBoxWords result.2 support.length))

theorem tail_code (support : List Nat) (N : Nat) :
    singleCorePresburgerTailCode support N=singleCorePresburgerEncode (tailFormula support N) := by
  induction support with
  | nil => rfl
  | cons i rest ih =>
    simp only [singleCorePresburgerTailCode,tailFormula,List.foldr_cons,singleCorePresburgerEncode] at ih ⊢
    rw [ih]

theorem point_code (support word : List Nat) :
    singleCorePresburgerPointCode support word=singleCorePresburgerEncode (pointFormula support word) := by
  have h (positions : List Nat) :
      positions.foldr (fun i rest => [(2,support.getD i 0,word.getD i 1)]++rest++[(6,0,0)])
        (singleCorePresburgerConstantCode true)=
      singleCorePresburgerEncode (positions.foldr
        (fun i rest => .conj (.equal (support.getD i 0) (word.getD i 1)) rest) (.truth true)) := by
    induction positions with
    | nil => rfl
    | cons i rest ih =>
      simp only [List.foldr_cons,singleCorePresburgerEncode]
      rw [ih]
  exact h _

theorem box_code (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat)
    (support : List Nat) (words : List (List Nat)) :
    words.foldr (fun word rest => if encodedSingleCoreBoxSign source row word=desired then
      singleCorePresburgerPointCode support word++rest++[(7,0,0)] else rest)
      (singleCorePresburgerConstantCode false)=
    singleCorePresburgerEncode (boxFormula source row desired support words) := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    by_cases h : encodedSingleCoreBoxSign source row word=desired
    · simp only [boxFormula,List.foldr_cons,if_pos h,singleCorePresburgerEncode]
      rw [ih,point_code]
      rfl
    · simp only [boxFormula,List.foldr_cons,if_neg h]
      exact ih

theorem output_code (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat) :
    encodedSingleCorePresburger source row desired=singleCorePresburgerEncode (compiledFormula source row desired) := by
  unfold encodedSingleCorePresburger compiledFormula
  dsimp only
  rw [tail_code,box_code]
  rfl

theorem tail_value (support : List Nat) (N : Nat) (ρ : Nat → Nat) :
    singleCorePresburgerValue (tailFormula support N) ρ=true ↔ ∃ i∈support,N≤ρ i := by
  induction support with
  | nil => simp [tailFormula,singleCorePresburgerValue]
  | cons i rest ih =>
    simp only [tailFormula,List.foldr_cons,singleCorePresburgerValue,Bool.or_eq_true,decide_eq_true_eq] at ih ⊢
    simpa only [List.mem_cons,exists_eq_or_imp] using (Iff.rfl : N≤ρ i ↔ N≤ρ i).or ih

theorem point_value (support word : List Nat) (ρ : Nat → Nat) :
    singleCorePresburgerValue (pointFormula support word) ρ=true ↔
      ∀ k : Nat,k<support.length → ρ (support.getD k 0)=word.getD k 1 := by
  have h (positions : List Nat) :
      singleCorePresburgerValue (positions.foldr
        (fun i rest => .conj (.equal (support.getD i 0) (word.getD i 1)) rest) (.truth true)) ρ=true ↔
      ∀ k∈positions,ρ (support.getD k 0)=word.getD k 1 := by
    induction positions with
    | nil => simp [singleCorePresburgerValue]
    | cons k rest ih =>
      simp only [List.foldr_cons,singleCorePresburgerValue,Bool.and_eq_true_iff,decide_eq_true_eq,List.forall_mem_cons,ih]
  simpa only [pointFormula,List.mem_range] using h (List.range support.length)

theorem box_value (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat)
    (support : List Nat) (words : List (List Nat)) (ρ : Nat → Nat) :
    singleCorePresburgerValue (boxFormula source row desired support words) ρ=true ↔
      ∃ word∈words,encodedSingleCoreBoxSign source row word=desired ∧
        ∀ k : Nat,k<support.length → ρ (support.getD k 0)=word.getD k 1 := by
  induction words with
  | nil => simp [boxFormula,singleCorePresburgerValue]
  | cons word rest ih =>
    simp only [boxFormula] at ih
    by_cases h : encodedSingleCoreBoxSign source row word=desired
    · simp only [boxFormula,List.foldr_cons,if_pos h,singleCorePresburgerValue,Bool.or_eq_true,point_value]
      simpa only [List.mem_cons,exists_eq_or_imp,h,true_and] using
        (Iff.refl (∀ k : Nat,k<support.length → ρ (support.getD k 0)=word.getD k 1)).or ih
    · simp only [boxFormula,List.foldr_cons,if_neg h]
      simpa only [List.mem_cons,exists_eq_or_imp,h,false_and,false_or] using ih

end LogicLineages.OrdinalComparison.SingleCorePresburger
