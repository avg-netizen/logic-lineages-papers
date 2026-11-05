module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSupportProof
open CommonLayerSyntax NormalForm SourceTermGraph SourceRows
open SourceTermGraphSupportProof

theorem bound_nil : SourceRows.Code.bound [] = 0 := rfl

theorem bound_cons (op : SourceTermGraph.Instruction)
    (ops : List SourceTermGraph.Instruction) :
    SourceRows.Code.bound (op :: ops) =
      max (SourceRows.Code.opBound op) (SourceRows.Code.bound ops) := rfl

theorem bound_append (xs ys : List SourceTermGraph.Instruction) :
    SourceRows.Code.bound (xs ++ ys) =
      max (SourceRows.Code.bound xs) (SourceRows.Code.bound ys) := by
  induction xs with
  | nil => simp only [List.nil_append, bound_nil, Nat.zero_max]
  | cons op xs ih =>
      simp only [List.cons_append, bound_cons, ih, max_assoc]

theorem bound_instructions_numeral (n : Nat) :
    SourceRows.Code.bound (instructions (.numeral n)) = 0 := by
  simp [instructions, SourceRows.Code.bound, SourceRows.Code.opBound]

theorem bound_instructions_variable (i : Nat) :
    SourceRows.Code.bound (instructions (.variable i)) = i + 1 := by
  simp [instructions, SourceRows.Code.bound, SourceRows.Code.opBound]

theorem bound_instructions_add (a b : BaseTerm) :
    SourceRows.Code.bound (instructions (.add a b)) =
      max (SourceRows.Code.bound (instructions a))
        (SourceRows.Code.bound (instructions b)) := by
  simp only [instructions, bound_append, bound_cons, bound_nil]
  simp [SourceRows.Code.opBound]

theorem bound_instructions_phi (a : BaseTerm) :
    SourceRows.Code.bound (instructions (.phi a)) =
      SourceRows.Code.bound (instructions a) := by
  simp only [instructions, bound_append, bound_cons, bound_nil]
  simp [SourceRows.Code.opBound]

/-- The bound is read from the literal variable instructions, not supplied
as an additional semantic parameter. Bound source occurrences are included. -/
theorem term_variable_lt_bound (t : BaseTerm) :
    ∀ i ∈ t.variables, i < SourceRows.Code.bound (instructions t) := by
  induction t with
  | numeral n =>
      intro i hi
      exact False.elim (List.not_mem_nil hi)
  | «variable» j =>
      intro i hi
      simp only [BaseTerm.variables, List.mem_singleton] at hi
      subst i
      rw [bound_instructions_variable]
      omega
  | add a b iha ihb =>
      intro i hi
      rw [bound_instructions_add]
      rcases List.mem_append.mp hi with ha | hb
      · exact lt_of_lt_of_le (iha i ha) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihb i hb) (le_max_right _ _)
  | phi a ih =>
      intro i hi
      rw [bound_instructions_phi]
      exact ih i hi

theorem localStart_fresh (a b : BaseTerm) :
    Fresh (localStart a b) (.add a b) := by
  intro i hi
  rcases List.mem_append.mp hi with ha | hb
  · exact lt_of_lt_of_le (term_variable_lt_bound a i ha) (le_max_left _ _)
  · exact lt_of_lt_of_le (term_variable_lt_bound b i hb) (le_max_right _ _)

theorem mem_bindAll_variables (xs : List Nat) (p : QFormula) (i : Nat) :
    i ∈ (bindAll xs p).variables ↔ i ∈ p.variables ∧ i ∉ xs := by
  induction xs with
  | nil => simp only [bindAll, List.foldr_nil, List.not_mem_nil, not_false_eq_true, and_true]
  | cons j xs ih =>
      change i ∈ (bindAll xs p).variables.filter (fun k => k != j) ↔ _
      simp only [List.mem_filter, bne_iff_ne, ih, List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨hp, hxs⟩, hne⟩
        exact ⟨hp, hne, hxs⟩
      · rintro ⟨hp, hne, hxs⟩
        exact ⟨⟨hp, hxs⟩, hne⟩

theorem relation_variables (strict : Bool) (x y i : Nat) :
    i ∈ (relation strict x y).variables ↔ i = x ∨ i = y := by
  cases strict with
  | false =>
      simp only [relation, Bool.false_eq_true, ↓reduceIte, mem_equation_variables,
        variableRow, rowVariables, List.map_cons, List.map_nil, Summand.name,
        List.mem_cons, List.not_mem_nil, or_false]
  | true =>
      simp only [relation, ↓reduceIte, NormalForm.Formula.variables, NormalForm.Atom.row,
        strictRow, rowVariables, List.map_cons, List.map_nil, Summand.name,
        List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

theorem atomBody_variables (strict : Bool) (a b : BaseTerm) (i : Nat) :
    i ∈ (atomBody strict a b).variables ↔
      i ∈ (BaseTerm.add a b).variables ∨
        i ∈ allocated (localStart a b) (.add a b) := by
  have hleft : output (localStart a b) a ∈
      allocated (localStart a b) (.add a b) := by
    rw [mem_allocated]
    have h := (mem_allocated (localStart a b) a _).mp
      (output_mem_allocated (localStart a b) a)
    simp only [nodeCount]
    omega
  have hright : output (localStart a b + nodeCount a) b ∈
      allocated (localStart a b) (.add a b) := by
    rw [mem_allocated]
    have h := (mem_allocated (localStart a b + nodeCount a) b _).mp
      (output_mem_allocated (localStart a b + nodeCount a) b)
    simp only [nodeCount]
    omega
  unfold atomBody
  simp only [NormalForm.Formula.variables, List.mem_append,
    exactGraphSupport (localStart a b) (.add a b) i, relation_variables]
  constructor
  · rintro (h | h | h)
    · exact h
    · subst i; exact Or.inr hleft
    · subst i; exact Or.inr hright
  · exact Or.inl

/-- Local binders remove every auxiliary and no original atom occurrence. -/
theorem exact_localAtom_variables (strict : Bool) (a b : BaseTerm) (i : Nat) :
    i ∈ (localAtom strict a b).variables ↔ i ∈ a.variables ++ b.variables := by
  unfold localAtom
  rw [mem_bindAll_variables]
  change (i ∈ (atomBody strict a b).variables ∧
    i ∉ allocated (localStart a b) (.add a b)) ↔ i ∈ (BaseTerm.add a b).variables
  rw [atomBody_variables]
  constructor
  · rintro ⟨h, hnot⟩
    exact h.resolve_right hnot
  · intro hi
    refine ⟨Or.inl hi, ?_⟩
    intro hnode
    have hsource := localStart_fresh a b i hi
    have hrange := (mem_allocated (localStart a b) (.add a b) i).mp hnode
    omega

theorem exactFreeVariableMembership : SourceRowsTargets.ExactFreeVariableMembership := by
  intro p
  induction p with
  | equal a b => intro i; exact exact_localAtom_variables false a b i
  | less a b => intro i; exact exact_localAtom_variables true a b i
  | negative p ih => intro i; exact ih i
  | conjunction p q ihp ihq =>
      intro i
      simp only [SourceRows.translate, QFormula.variables, SourceFormula.variables,
        List.mem_append, ihp, ihq]
  | existsNat j p ih =>
      intro i
      simp only [SourceRows.translate, QFormula.variables, SourceFormula.variables,
        List.mem_filter, ih]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSupportProof
