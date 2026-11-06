module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets

public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof

theorem nodeCount_pos (t : Expr) : 0 < nodeCount t := by
  cases t <;> simp [nodeCount]

theorem mem_names (start count i : Nat) :
    i ∈ names start count ↔ start ≤ i ∧ i < start + count := by
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hj' : j < count := List.mem_range.mp hj
    omega
  · rintro ⟨hlo,hhi⟩
    apply List.mem_map.mpr
    refine ⟨i-start,List.mem_range.mpr ?_,?_⟩ <;> omega

theorem mem_allocated (start : Nat) (t : Expr) (i : Nat) :
    i ∈ allocated start t ↔ start ≤ i ∧ i < start + nodeCount t :=
  mem_names start (nodeCount t) i

theorem names_nodup (start count : Nat) : (names start count).Nodup := by
  apply List.Nodup.map (fun a b h => Nat.add_left_cancel h)
  exact List.nodup_range

theorem names_add (start a b : Nat) :
    names start (a+b) = names start a ++ names (start+a) b := by
  simp only [names,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply,Nat.add_assoc]

theorem names_succ (start count : Nat) :
    names start (count+1) = names start count ++ [start+count] := by
  simp only [names,List.range_succ,List.map_append,List.map_cons,List.map_nil]

theorem output_mem_allocated (start : Nat) (t : Expr) :
    output start t ∈ allocated start t := by
  rw [mem_allocated]
  have ht := nodeCount_pos t
  unfold output
  omega

theorem allocated_add (start : Nat) (a b : Expr) :
    allocated start (.add a b) = allocated start a ++
      allocated (start+nodeCount a) b ++ [output start (.add a b)] := by
  have hout : output start (.add a b) = start+nodeCount a+nodeCount b := by
    simp only [output,nodeCount]
    omega
  rw [hout]
  simp only [allocated,nodeCount,names_succ,names_add,List.append_assoc,Nat.add_assoc]

theorem allocated_scale (start k : Nat) (a : Expr) :
    allocated start (.scale k a) = allocated start a ++ [output start (.scale k a)] := by
  have hout : output start (.scale k a) = start+nodeCount a := by
    simp only [output,nodeCount]
    omega
  rw [hout]
  simp only [allocated,nodeCount,names_succ]

theorem allocated_collapse (start code : Nat) (a : Expr) :
    allocated start (.collapse code a) =
      allocated start a ++ [output start (.collapse code a)] := by
  have hout : output start (.collapse code a) = start+nodeCount a := by
    simp only [output,nodeCount]
    omega
  rw [hout]
  simp only [allocated,nodeCount,names_succ]

theorem fresh_mono {start stop : Nat} {t : Expr} (h : start ≤ stop)
    (hf : Fresh start t) : Fresh stop t := by
  intro i hi
  exact lt_of_lt_of_le (hf i hi) h

theorem source_value_congr (t : Expr) (ν μ : Nat → Nat)
    (h : ∀ i ∈ t.variables, ν i = μ i) : t.value ν = t.value μ := by
  revert h
  induction t with
  | numeral n => intro h; rfl
  | «variable» i => intro h; exact h i (by simp [Expr.variables])
  | add a b iha ihb =>
      intro h
      have ha := iha (fun i hi => h i (List.mem_append_left _ hi))
      have hb := ihb (fun i hi => h i (List.mem_append_right _ hi))
      simp only [Expr.value,ha,hb]
  | scale k a ih => intro h; simp only [Expr.value,ih h]
  | collapse code a ih => intro h; simp only [Expr.value,ih h]

theorem exactAllocation : ExpressionTargets.ExactAllocation := by
  intro start t
  refine ⟨nodeCount_pos t,names_nodup start (nodeCount t),mem_allocated start t,?_⟩
  intro hf i hi hsource
  have hb := (mem_allocated start t i).mp hi
  have hs := hf i hsource
  omega

private theorem mem_le_maximum (xs : List Nat) (i : Nat) (hi : i ∈ xs) :
    i ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hi
  | cons a xs ih =>
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_max_left _ _
      · exact (ih hi).trans (le_max_right _ _)

theorem freshSymbolicOutput : ExpressionTargets.FreshSymbolicOutput := by
  intro t resultName
  have hf : Fresh (freshStart t resultName) t := by
    intro i hi
    have hle := mem_le_maximum t.variables i hi
    have hm := le_max_right resultName (t.variables.foldr max 0)
    unfold freshStart
    omega
  have hr : resultName < freshStart t resultName := by
    have hm := le_max_left resultName (t.variables.foldr max 0)
    unfold freshStart
    omega
  refine ⟨hf,hr,?_⟩
  intro hmem
  have h := (mem_allocated (freshStart t resultName) t resultName).mp hmem
  omega

theorem headEquation_support (code input resultName i : Nat)
    (hi : i ∈ rowVariables (headEquation code input resultName)) :
    i = input ∨ i = resultName := by
  obtain ⟨a,ha,hi⟩ := List.mem_map.mp hi
  change a ∈ (2,resultName,[]) ::
    (headRow code).2.map (fun b => (-b.1,input,b.2)) at ha
  rcases List.mem_cons.mp ha with ha | ha
  · subst a
    exact Or.inr hi.symm
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact Or.inl hi.symm

theorem rows_support (start : Nat) (t : Expr) (row : Row)
    (hr : row ∈ rows start t) (i : Nat) (hi : i ∈ rowVariables row) :
    i ∈ t.variables ∨ i ∈ allocated start t := by
  induction t generalizing start row with
  | numeral n =>
      have hrow : row = numeralRow start n := List.mem_singleton.mp hr
      subst row
      have he : i = start := by simpa [rowVariables,numeralRow] using hi
      subst i
      exact Or.inr ((mem_allocated start (.numeral n) start).mpr (by simp [nodeCount]))
  | «variable» j =>
      have hrow : row = variableRow start j := List.mem_singleton.mp hr
      subst row
      have he : i = start ∨ i = j := by simpa [rowVariables,variableRow] using hi
      rcases he with rfl | rfl
      · exact Or.inr ((mem_allocated start (.variable j) start).mpr (by simp [nodeCount]))
      · exact Or.inl (by simp [Expr.variables])
  | add a b iha ihb =>
      simp only [rows,List.mem_append,List.mem_singleton] at hr
      rcases hr with (hr | hr) | rfl
      · rcases iha start row hr hi with hs | hn
        · exact Or.inl (List.mem_append_left _ hs)
        · right
          have h := (mem_allocated start a i).mp hn
          rw [mem_allocated]
          simp only [nodeCount]
          omega
      · rcases ihb (start+nodeCount a) row hr hi with hs | hn
        · exact Or.inl (List.mem_append_right _ hs)
        · right
          have h := (mem_allocated (start+nodeCount a) b i).mp hn
          rw [mem_allocated]
          simp only [nodeCount]
          omega
      · have he : i = output start (.add a b) ∨ i = output start a ∨
            i = output (start+nodeCount a) b := by
          simpa [rowVariables,additionRow] using hi
        have ha := nodeCount_pos a
        have hb := nodeCount_pos b
        right
        rw [mem_allocated]
        simp only [nodeCount,output] at he ⊢
        omega
  | scale k a ih =>
      simp only [rows,List.mem_append,List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rcases ih start row hr hi with hs | hn
        · exact Or.inl hs
        · right
          have h := (mem_allocated start a i).mp hn
          rw [mem_allocated]
          simp only [nodeCount]
          omega
      · have he : i = output start (.scale k a) ∨ i = output start a := by
          simpa [rowVariables,scaleRow] using hi
        have ha := nodeCount_pos a
        right
        rw [mem_allocated]
        simp only [nodeCount,output] at he ⊢
        omega
  | collapse code a ih =>
      simp only [rows,List.mem_append,List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rcases ih start row hr hi with hs | hn
        · exact Or.inl hs
        · right
          have h := (mem_allocated start a i).mp hn
          rw [mem_allocated]
          simp only [nodeCount]
          omega
      · have he := headEquation_support code (output start a)
          (output start (.collapse code a)) i hi
        have ha := nodeCount_pos a
        right
        rw [mem_allocated]
        simp only [nodeCount,output] at he ⊢
        omega

theorem graphSupport : ExpressionTargets.GraphSupport := by
  refine ⟨rows_support,?_⟩
  intro t resultName row hr i hi
  change row ∈ rows (freshStart t resultName) t ++
    [variableRow resultName (output (freshStart t resultName) t)] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases rows_support (freshStart t resultName) t row hr i hi with hs | hn
    · exact Or.inl hs
    · exact Or.inr (Or.inr hn)
  · have hrow := List.mem_singleton.mp hr
    subst row
    have he : i = resultName ∨ i = output (freshStart t resultName) t := by
      simpa [rowVariables,variableRow] using hi
    rcases he with he | rfl
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (output_mem_allocated (freshStart t resultName) t))

theorem row_value_congr (row : Row) (ν μ : Nat → Nat)
    (h : ∀ i ∈ rowVariables row, ν i = μ i) : RowValue row ν = RowValue row μ := by
  unfold RowValue
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  change a.1 * (wordValue a.2.2 (ν a.2.1) : Int) =
    a.1 * (wordValue a.2.2 (μ a.2.1) : Int)
  have hn := h a.2.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)
  rw [hn]

theorem row_domain_congr (row : Row) (ν μ : Nat → Nat)
    (h : ∀ i ∈ rowVariables row, ν i = μ i) : RowDomain row ν ↔ RowDomain row μ := by
  constructor
  · intro hd a ha
    have hn := h a.2.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)
    rw [← hn]
    exact hd a ha
  · intro hd a ha
    have hn := h a.2.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)
    rw [hn]
    exact hd a ha

theorem rows_hold_congr (rs : List Row) (ν μ : Nat → Nat)
    (h : ∀ row ∈ rs, ∀ i ∈ rowVariables row, ν i = μ i) :
    RowsHold rs ν ↔ RowsHold rs μ := by
  constructor
  · intro hs row hr
    refine ⟨(row_domain_congr row ν μ (h row hr)).mp (hs row hr).1,?_⟩
    rw [← row_value_congr row ν μ (h row hr)]
    exact (hs row hr).2
  · intro hs row hr
    refine ⟨(row_domain_congr row ν μ (h row hr)).mpr (hs row hr).1,?_⟩
    rw [row_value_congr row ν μ (h row hr)]
    exact (hs row hr).2

theorem graph_holds_congr (start : Nat) (t : Expr) (ν μ : Nat → Nat)
    (h : ∀ i, i ∈ t.variables ∨ i ∈ allocated start t → ν i = μ i) :
    GraphHolds start t ν ↔ GraphHolds start t μ :=
  rows_hold_congr (rows start t) ν μ
    (fun row hr i hi => h i (rows_support start t row hr i hi))

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof
