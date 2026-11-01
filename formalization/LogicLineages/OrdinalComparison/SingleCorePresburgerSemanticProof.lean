module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerSyntaxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger

theorem row_tail_sign (row : SingleCoreRow) (hv : singleCoreRowValid row) (t : Nat)
    (ht : (encodedSingleCoreRowSign (singleCoreRowCode row)).2≤t) :
    singleCoreIntegerSign (actualSingleCoreRowValue row t)=(encodedSingleCoreRowSign (singleCoreRowCode row)).1 := by
  have h := (SingleCoreRowCompiler.sign.2 row hv).2.2 t ht
  by_cases hn : actualSingleCoreRowValue row t<0
  · have hs := h.1.mpr hn
    simp only [singleCoreIntegerSign,if_pos hn,hs]
  · by_cases hz : actualSingleCoreRowValue row t=0
    · have hs := h.2.1.mpr hz
      simp only [singleCoreIntegerSign,if_neg hn,if_pos hz,hs]
    · have hp : 0<actualSingleCoreRowValue row t := by omega
      have hs := h.2.2.mpr hp
      simp only [singleCoreIntegerSign,if_neg hn,if_neg hz,hs]

theorem core_tail_sign (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow)
    (hE : multivariatePositiveValid d E) (hrow : singleCoreRowValid row) (ρ : Nat → Nat)
    (h : ∃ i∈singleCoreSupport E,(encodedSingleCoreRowSign (singleCoreRowCode row)).2≤ρ i) :
    singleCoreIntegerSign (actualSingleCoreRowValue row (actualMultivariatePositiveEval E ρ))=
      (encodedSingleCoreRowSign (singleCoreRowCode row)).1 := by
  obtain ⟨i,hi,hN⟩ := h
  exact row_tail_sign row hrow _ (hN.trans (SingleCoreSupport.dominance d E hE ρ i hi))

theorem map_word_in_box (d : Nat) (E : MultivariatePositiveExpr) (hE : multivariatePositiveValid d E)
    (ρ : Nat → Nat) (hρ : ∀ i : Nat,i<d → 0<ρ i) (N : Nat)
    (hSmall : ∀ i∈singleCoreSupport E,ρ i<N) :
    (singleCoreSupport E).map ρ∈singleCoreBoxWords N (singleCoreSupport E).length := by
  apply (words_spec N _ _).mpr
  refine ⟨List.length_map _,?_⟩
  intro value hm
  obtain ⟨i,hi,heq⟩ := List.mem_map.mp hm
  subst value
  exact ⟨hρ i (SingleCoreSupport.bounds d E hE i hi).1,hSmall i hi⟩

theorem point_map (support : List Nat) (ρ : Nat → Nat) :
    singleCorePresburgerValue (pointFormula support (support.map ρ)) ρ=true := by
  apply (point_value _ _ _).mpr
  intro k hk
  rw [List.getD_eq_getElem support 0 hk,List.getD_eq_getElem _ 1 (by simpa using hk)]
  simp only [List.getElem_map]

theorem box_sign_agrees (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow)
    (hE : multivariatePositiveValid d E) (hrow : singleCoreRowValid row)
    (ρ : Nat → Nat) (N : Nat) (word : List Nat)
    (hWord : word∈singleCoreBoxWords N (singleCoreSupport E).length)
    (hPoint : ∀ k : Nat,k<(singleCoreSupport E).length →
      ρ ((singleCoreSupport E).getD k 0)=word.getD k 1) :
    encodedSingleCoreBoxSign (multivariatePositiveEncode E) (singleCoreRowCode row) word=
      singleCoreIntegerSign (actualSingleCoreRowValue row (actualMultivariatePositiveEval E ρ)) := by
  have hPositive := fun value hv => ((words_spec N _ word).mp hWord).2 value hv |>.1
  rw [box_sign d E row hE hrow word hPositive]
  have hAgree := SingleCoreSupport.agreement E (singleCoreBoxLookup (singleCoreSupport E) word) ρ
    (lookup_agreement (singleCoreSupport E) word ρ hPoint)
  rw [hAgree]

theorem output_value (d : Nat) (E : MultivariatePositiveExpr) (row : SingleCoreRow)
    (hE : multivariatePositiveValid d E) (hrow : singleCoreRowValid row)
    (desired : Nat) (ρ : Nat → Nat) (hρ : ∀ i : Nat,i<d → 0<ρ i) :
    singleCorePresburgerValue (compiledFormula (multivariatePositiveEncode E) (singleCoreRowCode row) desired) ρ=true ↔
      singleCoreIntegerSign (actualSingleCoreRowValue row (actualMultivariatePositiveEval E ρ))=desired := by
  unfold compiledFormula
  rw [SingleCoreSupport.source E]
  dsimp only
  rw [singleCorePresburgerValue,Bool.or_eq_true,singleCorePresburgerValue,Bool.and_eq_true_iff,
    tail_value,singleCorePresburgerValue,decide_eq_true_eq,box_value]
  constructor
  · rintro (⟨hTail,hSign⟩ | ⟨word,hWord,hSign,hPoint⟩)
    · exact (core_tail_sign d E row hE hrow ρ hTail).trans hSign
    · exact (box_sign_agrees d E row hE hrow ρ _ word hWord hPoint).symm.trans hSign
  · intro hSign
    by_cases hTail : ∃ i∈singleCoreSupport E,(encodedSingleCoreRowSign (singleCoreRowCode row)).2≤ρ i
    · exact Or.inl ⟨hTail,(core_tail_sign d E row hE hrow ρ hTail).symm.trans hSign⟩
    · have hSmall : ∀ i∈singleCoreSupport E,ρ i<(encodedSingleCoreRowSign (singleCoreRowCode row)).2 := by
        intro i hi
        by_contra hn
        exact hTail ⟨i,hi,Nat.le_of_not_gt hn⟩
      have hWord := map_word_in_box d E hE ρ hρ _ hSmall
      have hPoint := (point_value _ _ _).mp (point_map (singleCoreSupport E) ρ)
      exact Or.inr ⟨_,hWord,(box_sign_agrees d E row hE hrow ρ _ _ hWord hPoint).trans hSign,hPoint⟩

theorem universal_correct : Targets.ActualSingleCoreUniversal := by
  intro d E row hE hrow allowed
  unfold encodedSingleCoreUniversal
  rw [SingleCoreSupport.source E]
  dsimp only
  rw [Bool.and_eq_true_iff,Bool.or_eq_true,decide_eq_true_eq,List.all_eq_true]
  constructor
  · rintro ⟨hTail,hBox⟩ ρ hρ
    by_cases hLarge : ∃ i∈singleCoreSupport E,(encodedSingleCoreRowSign (singleCoreRowCode row)).2≤ρ i
    · have hAllowed : (encodedSingleCoreRowSign (singleCoreRowCode row)).1∈allowed := by
        rcases hTail with hEmpty | hAllowed
        · have he : singleCoreSupport E=[] := List.isEmpty_iff.mp hEmpty
          obtain ⟨i,hi,hN⟩ := hLarge
          rw [he] at hi
          cases hi
        · exact hAllowed
      rw [core_tail_sign d E row hE hrow ρ hLarge]
      exact hAllowed
    · have hSmall : ∀ i∈singleCoreSupport E,ρ i<(encodedSingleCoreRowSign (singleCoreRowCode row)).2 := by
        intro i hi
        by_contra hn
        exact hLarge ⟨i,hi,Nat.le_of_not_gt hn⟩
      have hWord := map_word_in_box d E hE ρ hρ _ hSmall
      have hPoint := (point_value _ _ _).mp (point_map (singleCoreSupport E) ρ)
      have h := of_decide_eq_true (hBox _ hWord)
      rwa [box_sign_agrees d E row hE hrow ρ _ _ hWord hPoint] at h
  · intro h
    constructor
    · by_cases hEmpty : singleCoreSupport E=[]
      · exact Or.inl (by rw [hEmpty]; rfl)
      · obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil (singleCoreSupport E) hEmpty
        have hN : 0<(encodedSingleCoreRowSign (singleCoreRowCode row)).2 := (SingleCoreRowCompiler.sign.2 row hrow).2.1
        have hAll := h (fun _ => (encodedSingleCoreRowSign (singleCoreRowCode row)).2) (fun i hi => hN)
        have hLarge : ∃ i∈singleCoreSupport E,(encodedSingleCoreRowSign (singleCoreRowCode row)).2≤
            (fun _ : Nat => (encodedSingleCoreRowSign (singleCoreRowCode row)).2) i := ⟨i,hi,le_rfl⟩
        rw [core_tail_sign d E row hE hrow _ hLarge] at hAll
        exact Or.inr hAll
    · intro word hWord
      have hPositive := fun value hv => ((words_spec _ _ word).mp hWord).2 value hv |>.1
      have hρ : ∀ i : Nat,i<d → 0<singleCoreBoxLookup (singleCoreSupport E) word i :=
        fun i hi => lookup_positive (singleCoreSupport E) word hPositive i
      have hAll := h _ hρ
      apply decide_eq_true_eq.mpr
      rwa [box_sign d E row hE hrow word hPositive]

end LogicLineages.OrdinalComparison.SingleCorePresburger
