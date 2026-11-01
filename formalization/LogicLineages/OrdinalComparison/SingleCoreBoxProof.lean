module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerTargets
public import LogicLineages.OrdinalComparison.SingleCoreSupportProof
public import LogicLineages.OrdinalComparison.SingleCoreEvaluationProof
public import LogicLineages.OrdinalComparison.SingleCoreRowProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger

theorem words_spec (bound length : Nat) (word : List Nat) :
    word∈singleCoreBoxWords bound length ↔ word.length=length ∧ ∀ value∈word,0<value ∧ value<bound := by
  induction length generalizing word with
  | zero =>
    constructor
    · intro h
      have he : word=[] := List.mem_singleton.mp h
      subst word
      exact ⟨rfl,fun value hv => by cases hv⟩
    · rintro ⟨hl,hv⟩
      have he : word=[] := List.eq_nil_of_length_eq_zero hl
      subst word
      exact List.mem_singleton_self _
  | succ length ih =>
    constructor
    · intro h
      obtain ⟨value,hvalue,hm⟩ := List.mem_flatMap.mp h
      obtain ⟨rest,hrest,heq⟩ := List.mem_map.mp hm
      subst word
      have hr := (ih rest).mp hrest
      have hb := List.mem_range.mp hvalue
      refine ⟨by simp [hr.1],?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · omega
      · exact hr.2 v hv
    · rintro ⟨hlen,hvalues⟩
      cases word with
      | nil => simp at hlen
      | cons value rest =>
        have hFirst := hvalues value List.mem_cons_self
        have hRest : rest∈singleCoreBoxWords bound length := (ih rest).mpr
          ⟨by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen,
            fun v hv => hvalues v (List.mem_cons_of_mem _ hv)⟩
        apply List.mem_flatMap.mpr
        refine ⟨value-1,List.mem_range.mpr (by omega),?_⟩
        apply List.mem_map.mpr
        refine ⟨rest,hRest,?_⟩
        rw [Nat.sub_add_cancel (by omega)]

theorem lookup_positive (support word : List Nat) (h : ∀ value∈word,0<value) (i : Nat) :
    0<singleCoreBoxLookup support word i := by
  unfold singleCoreBoxLookup
  by_cases hb : support.findIdx (fun j => decide (j=i))<word.length
  · rw [List.getD_eq_getElem word 1 hb]
    exact h _ (List.getElem_mem hb)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hb)]
    exact Nat.zero_lt_one

theorem lookup_index (support : List Nat) (i : Nat) (hi : i∈support) :
    ∃ k : Nat,k<support.length ∧ support.getD k 0=i ∧ k=support.findIdx (fun j => decide (j=i)) := by
  have hlt : support.findIdx (fun j => decide (j=i))<support.length :=
    List.findIdx_lt_length_of_exists ⟨i,hi,by simp⟩
  refine ⟨_,hlt,?_,rfl⟩
  rw [List.getD_eq_getElem support 0 hlt]
  exact of_decide_eq_true (List.findIdx_getElem (w := hlt))

theorem lookup_agreement (support word : List Nat) (ρ : Nat → Nat)
    (h : ∀ k : Nat,k<support.length → ρ (support.getD k 0)=word.getD k 1) :
    ∀ i∈support,singleCoreBoxLookup support word i=ρ i := by
  intro i hi
  obtain ⟨k,hk,hvalue,hindex⟩ := lookup_index support i hi
  unfold singleCoreBoxLookup
  rw [←hindex,←h k hk,hvalue]

theorem lookup_map (support : List Nat) (ρ : Nat → Nat) :
    ∀ i∈support,singleCoreBoxLookup support (support.map ρ) i=ρ i := by
  apply lookup_agreement
  intro k hk
  rw [List.getD_eq_getElem support 0 hk,List.getD_eq_getElem _ 1 (by simpa using hk)]
  simp only [List.getElem_map]

theorem tuple_value (source : Nat) (support word : List Nat)
    (hPositive : ∀ value∈word,0<value) (i : Nat) (hi : i≤source) :
    (singleCoreBoxTuple source support word).getD i 0+1=singleCoreBoxLookup support word i := by
  unfold singleCoreBoxTuple
  rw [List.getD_eq_getElem _ 0 (by simp; omega)]
  simp only [List.getElem_map,List.getElem_range]
  have hp := lookup_positive support word hPositive i
  omega

theorem core_box_value (d : Nat) (E : MultivariatePositiveExpr) (hv : multivariatePositiveValid d E)
    (word : List Nat) (hPositive : ∀ value∈word,0<value) :
    encodedSingleCoreEvaluation (multivariatePositiveEncode E)
      (singleCoreBoxTuple (multivariatePositiveEncode E) (singleCoreSupport E) word)=
        actualMultivariatePositiveEval E (singleCoreBoxLookup (singleCoreSupport E) word) := by
  rw [SingleCoreEvaluation.actual_value]
  apply SingleCoreSupport.agreement
  intro i hi
  exact tuple_value _ _ _ hPositive i (SingleCoreSupport.bounds d E hv i hi).2

theorem row_point (row : SingleCoreRow) (hv : singleCoreRowValid row) (t : Nat) :
    encodedSingleCoreRowPoint (singleCoreRowCode row) t=singleCoreIntegerSign (actualSingleCoreRowValue row t) := by
  have hp := SingleCoreRowCompiler.parts_program.2.2 row
  unfold encodedSingleCoreRowPoint
  rw [hp]
  dsimp only
  rw [encodedPositiveEvaluationCorrect (singleCoreRowPart false row) t,
    encodedPositiveEvaluationCorrect (singleCoreRowPart true row) t,
    SingleCoreRowCompiler.semantics row hv |>.2.2 t]
  unfold comparisonNaturalSign singleCoreIntegerSign
  by_cases hlt : actualFixedLimitProfileEval (singleCoreRowPart false row) t<
      actualFixedLimitProfileEval (singleCoreRowPart true row) t
  · have hi : (actualFixedLimitProfileEval (singleCoreRowPart false row) t : Int)-
        (actualFixedLimitProfileEval (singleCoreRowPart true row) t : Int)<0 := by omega
    simp only [if_pos hlt,if_pos hi]
  · have hn : ¬((actualFixedLimitProfileEval (singleCoreRowPart false row) t : Int)-
        (actualFixedLimitProfileEval (singleCoreRowPart true row) t : Int)<0) := by omega
    by_cases he : actualFixedLimitProfileEval (singleCoreRowPart false row) t=
        actualFixedLimitProfileEval (singleCoreRowPart true row) t
    · simp only [if_neg hlt,if_neg hn,he,lt_self_iff_false,ite_false,sub_self,if_true]
    · have hgt : actualFixedLimitProfileEval (singleCoreRowPart true row) t<
          actualFixedLimitProfileEval (singleCoreRowPart false row) t := by omega
      have hne : (actualFixedLimitProfileEval (singleCoreRowPart false row) t : Int)-
          (actualFixedLimitProfileEval (singleCoreRowPart true row) t : Int)≠0 := by omega
      simp only [if_neg hlt,if_pos hgt,if_neg hn,if_neg hne]

theorem box_sign (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow)
    (hE : multivariatePositiveValid d E) (hrow : singleCoreRowValid row)
    (word : List Nat) (hPositive : ∀ value∈word,0<value) :
    encodedSingleCoreBoxSign (multivariatePositiveEncode E) (singleCoreRowCode row) word=
      singleCoreIntegerSign (actualSingleCoreRowValue row
        (actualMultivariatePositiveEval E (singleCoreBoxLookup (singleCoreSupport E) word))) := by
  unfold encodedSingleCoreBoxSign
  rw [SingleCoreSupport.source E]
  dsimp only
  rw [core_box_value d E hE word hPositive,row_point row hrow]

end LogicLineages.OrdinalComparison.SingleCorePresburger
