module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof
open CommonLayerSyntax NormalForm SourceTermGraph

theorem nodeCount_pos (t : BaseTerm) : 0 < nodeCount t := by
  cases t <;> simp [nodeCount]

theorem mem_names (start count i : Nat) :
    i ∈ names start count ↔ start ≤ i ∧ i < start + count := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj' : j < count := List.mem_range.mp hj
    omega
  · rintro ⟨hlo, hhi⟩
    apply List.mem_map.mpr
    refine ⟨i - start, List.mem_range.mpr ?_, ?_⟩ <;> omega

theorem mem_allocated (start : Nat) (t : BaseTerm) (i : Nat) :
    i ∈ allocated start t ↔ start ≤ i ∧ i < start + nodeCount t :=
  mem_names start (nodeCount t) i

theorem names_nodup (start count : Nat) : (names start count).Nodup := by
  apply List.Nodup.map (fun a b h => Nat.add_left_cancel h)
  exact List.nodup_range

theorem names_add (start a b : Nat) :
    names start (a + b) = names start a ++ names (start + a) b := by
  simp only [names, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, Nat.add_assoc]

theorem names_succ (start count : Nat) :
    names start (count + 1) = names start count ++ [start + count] := by
  simp only [names, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem output_mem_allocated (start : Nat) (t : BaseTerm) :
    output start t ∈ allocated start t := by
  rw [mem_allocated]
  have ht := nodeCount_pos t
  unfold output
  omega

theorem allocated_add (start : Nat) (a b : BaseTerm) :
    allocated start (.add a b) = allocated start a ++
      allocated (start + nodeCount a) b ++ [output start (.add a b)] := by
  have hout : output start (.add a b) = start + nodeCount a + nodeCount b := by
    simp only [output, nodeCount]
    omega
  rw [hout]
  simp only [allocated, nodeCount, names_succ, names_add, List.append_assoc,
    Nat.add_assoc]

theorem allocated_phi (start : Nat) (a : BaseTerm) :
    allocated start (.phi a) = allocated start a ++ [output start (.phi a)] := by
  have hout : output start (.phi a) = start + nodeCount a := by
    simp only [output, nodeCount]
    omega
  rw [hout]
  simp only [allocated, nodeCount, names_succ]

theorem fresh_mono {start stop : Nat} {t : BaseTerm} (h : start ≤ stop)
    (hf : Fresh start t) : Fresh stop t := by
  intro i hi
  exact lt_of_lt_of_le (hf i hi) h

theorem source_value_congr (t : BaseTerm) (ν μ : Nat → Nat)
    (h : ∀ i ∈ t.variables, ν i = μ i) : t.value ν = t.value μ :=
  BaseTermPrograms.Proof.supportStability t ν μ h

theorem exactAllocation : SourceTermGraphTargets.ExactAllocation := by
  intro start t
  refine ⟨nodeCount_pos t, names_nodup start (nodeCount t), mem_allocated start t, ?_⟩
  intro hf i hi hsource
  have hb := (mem_allocated start t i).mp hi
  have hs := hf i hsource
  omega

theorem negateRow_variables (row : Row) :
    rowVariables (SourceTermGraph.negateRow row) = rowVariables row := by
  simp only [rowVariables, SourceTermGraph.negateRow, List.map_map]
  rfl

theorem equation_variables (row : Row) :
    (equation row).variables = rowVariables row ++ rowVariables row := by
  simp only [equation, NormalForm.Formula.variables, NormalForm.Atom.row,
    negateRow_variables]

theorem mem_equation_variables (row : Row) (i : Nat) :
    i ∈ (equation row).variables ↔ i ∈ rowVariables row := by
  rw [equation_variables, List.mem_append]
  simp only [or_self]

theorem equations_cons_variables (row : Row) (rest : List Row) :
    (equations (row :: rest)).variables =
      (equation row).variables ++ (equations rest).variables := rfl

theorem equations_append_variables (a b : List Row) :
    (equations (a ++ b)).variables =
      (equations a).variables ++ (equations b).variables := by
  induction a with
  | nil => simp only [List.nil_append, equations, List.foldr_nil,
      NormalForm.Formula.variables]
  | cons row rest ih =>
      simp only [List.cons_append, equations_cons_variables, ih, List.append_assoc]

theorem equations_singleton_variables (row : Row) (i : Nat) :
    i ∈ (equations [row]).variables ↔ i ∈ rowVariables row := by
  change i ∈ (equation row).variables ++ [] ↔ _
  simp only [List.append_nil, mem_equation_variables]

theorem exactGraphSupport : SourceTermGraphTargets.ExactGraphSupport := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro i
      simp only [graph, rows, equations_singleton_variables, numeralRow, rowVariables,
        List.map_cons, List.map_nil, Summand.name, BaseTerm.variables, List.not_mem_nil,
        false_or, List.mem_singleton, mem_allocated, nodeCount]
      omega
  | «variable» j =>
      intro i
      simp only [graph, rows, equations_singleton_variables, variableRow, rowVariables,
        List.map_cons, List.map_nil, Summand.name, BaseTerm.variables, List.mem_cons,
        List.not_mem_nil, or_false, mem_allocated, nodeCount]
      omega
  | add a b iha ihb =>
      intro i
      have ha := nodeCount_pos a
      have hb := nodeCount_pos b
      change i ∈ (equations (rows start a ++ rows (start + nodeCount a) b ++
        [additionRow (output start (.add a b)) (output start a)
          (output (start + nodeCount a) b)])).variables ↔ _
      simp only [equations_append_variables, List.mem_append, equations_singleton_variables,
        additionRow, rowVariables, List.map_cons, List.map_nil, Summand.name,
        List.mem_cons, List.not_mem_nil, or_false]
      change (((i ∈ (graph start a).variables) ∨
        (i ∈ (graph (start + nodeCount a) b).variables)) ∨
        (i = output start (.add a b) ∨ i = output start a ∨
          i = output (start + nodeCount a) b)) ↔ _
      rw [iha, ihb]
      simp only [BaseTerm.variables, List.mem_append, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;> by_cases hib : i ∈ b.variables <;>
        simp only [hia, hib, true_or, or_true, false_or, or_false] <;> omega
  | phi a ih =>
      intro i
      have ha := nodeCount_pos a
      change i ∈ (equations (rows start a ++
        [phiRow (output start (.phi a)) (output start a)])).variables ↔ _
      simp only [equations_append_variables, List.mem_append, equations_singleton_variables,
        phiRow, rowVariables, List.map_cons, List.map_nil, Summand.name,
        List.mem_cons, List.not_mem_nil, or_false]
      change (i ∈ (graph start a).variables ∨
        i = output start (.phi a) ∨ i = output start a) ↔ _
      rw [ih]
      simp only [BaseTerm.variables, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;>
        simp only [hia, true_or, or_true, false_or, or_false] <;> omega

theorem negateRow_meaningful (row : Row) (ν : Nat → Nat) :
    rowMeaningful (SourceTermGraph.negateRow row) ν ↔ rowMeaningful row ν := by
  constructor
  · intro h a ha
    exact h (-a.1, a.2) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact h b hb

private theorem numeralRow_meaningful (z n : Nat) (ν : Nat → Nat) :
    rowMeaningful (numeralRow z n) ν := by
  simp [rowMeaningful, numeralRow, Summand.meaningful]

private theorem variableRow_meaningful (z i : Nat) (ν : Nat → Nat) :
    rowMeaningful (variableRow z i) ν := by
  simp [rowMeaningful, variableRow, Summand.meaningful]

private theorem additionRow_meaningful (z x y : Nat) (ν : Nat → Nat) :
    rowMeaningful (additionRow z x y) ν := by
  simp [rowMeaningful, additionRow, Summand.meaningful]

private theorem phiRow_meaningful (z x : Nat) (ν : Nat → Nat) :
    rowMeaningful (phiRow z x) ν := by
  simp [rowMeaningful, phiRow, Summand.meaningful]

theorem originalGraphDomains : SourceTermGraphTargets.OriginalGraphDomains := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro row h ν
      simp only [rows, List.mem_singleton] at h
      subst row
      have h := numeralRow_meaningful start n ν
      exact ⟨h, (negateRow_meaningful _ _).mpr h⟩
  | «variable» i =>
      intro row h ν
      simp only [rows, List.mem_singleton] at h
      subst row
      have h := variableRow_meaningful start i ν
      exact ⟨h, (negateRow_meaningful _ _).mpr h⟩
  | add a b iha ihb =>
      intro row h ν
      simp only [rows, List.mem_append, List.mem_singleton] at h
      rcases h with (h | h) | h
      · exact iha start row h ν
      · exact ihb (start + nodeCount a) row h ν
      · subst row
        have h := additionRow_meaningful (output start (.add a b))
          (output start a) (output (start + nodeCount a) b) ν
        exact ⟨h, (negateRow_meaningful _ _).mpr h⟩
  | phi a ih =>
      intro row h ν
      simp only [rows, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact ih start row h ν
      · subst row
        have h := phiRow_meaningful (output start (.phi a)) (output start a) ν
        exact ⟨h, (negateRow_meaningful _ _).mpr h⟩

theorem summand_value_congr (s : Summand) (ν μ : Nat → Nat)
    (h : ν s.name = μ s.name) : s.term.value ν = s.term.value μ := by
  cases s with
  | «variable» i => exact h
  | phi i e =>
      change ν i = μ i at h
      simp only [Summand.term, Term.value, shiftTerm, h]
  | hyperPhi i e h' =>
      change ν i = μ i at h
      simp only [Summand.term, HyperWindow.valueTerm, HyperWindow.innerTerm,
        HyperWindow.indexTerm, Term.value, shiftTerm, h]

theorem row_value_congr (row : Row) (ν μ : Nat → Nat)
    (h : ∀ i ∈ rowVariables row, ν i = μ i) : rowValue row ν = rowValue row μ := by
  unfold rowValue
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have hn : ν a.2.name = μ a.2.name := h a.2.name (List.mem_map.mpr ⟨a, ha, rfl⟩)
  rw [summand_value_congr a.2 ν μ hn]

theorem formula_eval_congr (p : NormalForm.Formula) (ν μ : Nat → Nat)
    (h : ∀ i ∈ p.variables, ν i = μ i) : p.eval ν ↔ p.eval μ := by
  revert h
  induction p with
  | truth => intro h; rfl
  | falsity => intro h; rfl
  | atom a =>
      intro h
      cases a with
      | nonnegative row =>
          change (0 ≤ rowValue row ν) ↔ (0 ≤ rowValue row μ)
          rw [row_value_congr row ν μ h]
      | divisible m row =>
          change (((m + 1 : Nat) : Int) ∣ rowValue row ν) ↔
            (((m + 1 : Nat) : Int) ∣ rowValue row μ)
          rw [row_value_congr row ν μ h]
  | negative p ih => intro h; exact not_congr (ih h)
  | conjunction p q ihp ihq =>
      intro h
      exact and_congr
        (ihp (fun i hi => h i (List.mem_append_left _ hi)))
        (ihq (fun i hi => h i (List.mem_append_right _ hi)))
  | disjunction p q ihp ihq =>
      intro h
      exact or_congr
        (ihp (fun i hi => h i (List.mem_append_left _ hi)))
        (ihq (fun i hi => h i (List.mem_append_right _ hi)))

theorem graph_eval_congr (start : Nat) (t : BaseTerm) (ν μ : Nat → Nat)
    (h : ∀ i, i ∈ t.variables ∨ i ∈ allocated start t → ν i = μ i) :
    (graph start t).eval ν ↔ (graph start t).eval μ :=
  formula_eval_congr (graph start t) ν μ
    (fun i hi => h i ((exactGraphSupport start t i).mp hi))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof
