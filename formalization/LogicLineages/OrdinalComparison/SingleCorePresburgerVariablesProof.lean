module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerSyntaxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger

theorem tail_variables (support : List Nat) (N : Nat) :
    singleCorePresburgerVariables (tailFormula support N)=support := by
  induction support with
  | nil => rfl
  | cons i rest ih =>
    simp only [tailFormula,List.foldr_cons,singleCorePresburgerVariables,List.singleton_append] at ih ⊢
    rw [ih]

theorem point_variables (support word : List Nat) :
    singleCorePresburgerVariables (pointFormula support word)=support := by
  have h (positions : List Nat) :
      singleCorePresburgerVariables (positions.foldr
        (fun i rest => .conj (.equal (support.getD i 0) (word.getD i 1)) rest) (.truth true))=
      positions.map (fun i => support.getD i 0) := by
    induction positions with
    | nil => rfl
    | cons i rest ih =>
      simp only [List.foldr_cons,singleCorePresburgerVariables,List.singleton_append,List.map_cons,ih]
  rw [pointFormula,h]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro i hi hk
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem support 0 hk

theorem box_variables (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat)
    (support : List Nat) (words : List (List Nat)) :
    ∀ i∈singleCorePresburgerVariables (boxFormula source row desired support words),i∈support := by
  induction words with
  | nil => intro i hi; cases hi
  | cons word rest ih =>
    intro i hi
    by_cases h : encodedSingleCoreBoxSign source row word=desired
    · change i∈singleCorePresburgerVariables
        (if encodedSingleCoreBoxSign source row word=desired then
          .disj (pointFormula support word) (boxFormula source row desired support rest)
        else boxFormula source row desired support rest) at hi
      rw [if_pos h,singleCorePresburgerVariables,point_variables] at hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hi
      · exact ih i hi
    · change i∈singleCorePresburgerVariables
        (if encodedSingleCoreBoxSign source row word=desired then
          .disj (pointFormula support word) (boxFormula source row desired support rest)
        else boxFormula source row desired support rest) at hi
      rw [if_neg h] at hi
      exact ih i hi

theorem compiled_variables (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat) :
    ∀ i∈singleCorePresburgerVariables (compiledFormula source row desired),i∈encodedSingleCoreSupport source := by
  intro i hi
  unfold compiledFormula at hi
  dsimp only at hi
  simp only [singleCorePresburgerVariables,tail_variables,List.append_nil] at hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hi
  · exact box_variables source row desired _ _ i hi

end LogicLineages.OrdinalComparison.SingleCorePresburger
