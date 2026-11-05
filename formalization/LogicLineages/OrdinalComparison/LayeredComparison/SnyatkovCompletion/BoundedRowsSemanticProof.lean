module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof
open NormalForm BoundedRows

theorem valueAt_update (s : Summand) (i n : Nat) (ν : Nat → Nat)
    (hi : s.name = i) :
    s.term.value (Function.update ν i n) = valueAt s n := by
  apply SourceTermGraphSupportProof.summand_value_congr
  simp only [hi, Function.update_self]

theorem value_update_other (s : Summand) (i n : Nat) (ν : Nat → Nat)
    (hi : s.name ≠ i) :
    s.term.value (Function.update ν i n) = s.term.value ν :=
  SourceTermGraphSupportProof.summand_value_congr s _ _ (Function.update_of_ne hi _ _)

theorem splitItems_nil (i n : Nat) : splitItems i n [] = (0, []) := rfl

theorem splitItems_cons (i n : Nat) (a : Int × Summand) (xs : List (Int × Summand)) :
    splitItems i n (a :: xs) =
      if a.2.name = i then
        (a.1 * (valueAt a.2 n : Int) + (splitItems i n xs).1, (splitItems i n xs).2)
      else ((splitItems i n xs).1, a :: (splitItems i n xs).2) := rfl

theorem splitItems_value (i n : Nat) (xs : List (Int × Summand)) (ν : Nat → Nat) :
    (splitItems i n xs).1 +
        ((splitItems i n xs).2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      (xs.map (fun a => a.1 * (a.2.term.value (Function.update ν i n) : Int))).sum := by
  induction xs with
  | nil => simp only [splitItems_nil, List.map_nil, List.sum_nil, add_zero]
  | cons a xs ih =>
      by_cases hi : a.2.name = i
      · have hv := valueAt_update a.2 i n ν hi
        simp only [splitItems_cons, if_pos hi, List.map_cons, List.sum_cons, hv]
        omega
      · have hv := value_update_other a.2 i n ν hi
        simp only [splitItems_cons, if_neg hi, List.map_cons, List.sum_cons, hv]
        omega

theorem actualRowSubstitution : BoundedRowsTargets.ActualRowSubstitution := by
  intro i n row ν
  have h := splitItems_value i n row.2 ν
  simp only [rowSubstitute, rowValue]
  omega

theorem splitItems_remaining (i n : Nat) (xs : List (Int × Summand)) :
    (splitItems i n xs).2 = xs.filter (fun a => a.2.name != i) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases hi : a.2.name = i
      · simp [splitItems_cons, hi, ih]
      · simp [splitItems_cons, hi, ih]

theorem exactResidualOccurrences : BoundedRowsTargets.ExactResidualOccurrences := by
  intro i n row
  exact splitItems_remaining i n row.2

theorem residual_mem (i n : Nat) (row : Row) (a : Int × Summand) :
    a ∈ (rowSubstitute i n row).2 ↔ a ∈ row.2 ∧ a.2.name ≠ i := by
  rw [exactResidualOccurrences i n row]
  simp only [List.mem_filter, bne_iff_ne]

theorem fixedCutoff_le (i n : Nat) (row : Row) :
    fixedCutoff i row ≤ n ↔
      ∀ a ∈ row.2, a.2.name = i → a.2.domainCutoff ≤ n := by
  rcases row with ⟨c, xs⟩
  change xs.foldr (fun a rest => max (if a.2.name = i then a.2.domainCutoff else 0) rest) 0 ≤ n ↔
    ∀ a ∈ xs, a.2.name = i → a.2.domainCutoff ≤ n
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.foldr_cons, max_le_iff, ih]
      constructor
      · rintro ⟨hhead, htail⟩ b hb hname
        rcases List.mem_cons.mp hb with hb | hb
        · subst b
          simpa only [if_pos hname] using hhead
        · exact htail b hb hname
      · intro h
        refine ⟨?_, fun b hb hname => h b (List.mem_cons_of_mem a hb) hname⟩
        by_cases hname : a.2.name = i
        · simpa only [if_pos hname] using h a List.mem_cons_self hname
        · simp only [if_neg hname, Nat.zero_le]

theorem exactOriginalDomains : BoundedRowsTargets.ExactOriginalDomains := by
  intro i n row ν
  rw [fixedCutoff_le i n row]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha hname
      have hc := (NormalFormSemanticProof.exactOriginalDomainCutoffs a.2
        (Function.update ν i n)).mp (h a ha)
      simpa only [hname, Function.update_self] using hc
    · intro a ha
      obtain ⟨hsource, hname⟩ := (residual_mem i n row a).mp ha
      apply (NormalFormSemanticProof.exactOriginalDomainCutoffs a.2 ν).mpr
      have hc := (NormalFormSemanticProof.exactOriginalDomainCutoffs a.2
        (Function.update ν i n)).mp (h a hsource)
      simpa only [Function.update_of_ne hname] using hc
  · rintro ⟨hfixed, hrest⟩ a ha
    apply (NormalFormSemanticProof.exactOriginalDomainCutoffs a.2
      (Function.update ν i n)).mpr
    by_cases hname : a.2.name = i
    · simpa only [hname, Function.update_self] using hfixed a ha hname
    · have hm := hrest a ((residual_mem i n row a).mpr ⟨ha, hname⟩)
      have hc := (NormalFormSemanticProof.exactOriginalDomainCutoffs a.2 ν).mp hm
      simpa only [Function.update_of_ne hname] using hc

theorem atom_substitution (i n : Nat) (a : Atom) (ν : Nat → Nat) :
    (atomSubstitute i n a).eval ν ↔ a.eval (Function.update ν i n) := by
  cases a with
  | nonnegative row =>
      change (0 ≤ rowValue (rowSubstitute i n row) ν) ↔
        (0 ≤ rowValue row (Function.update ν i n))
      rw [actualRowSubstitution i n row ν]
  | divisible m row =>
      change (((m + 1 : Nat) : Int) ∣ rowValue (rowSubstitute i n row) ν) ↔
        (((m + 1 : Nat) : Int) ∣ rowValue row (Function.update ν i n))
      rw [actualRowSubstitution i n row ν]

theorem actualFormulaSubstitution : BoundedRowsTargets.ActualFormulaSubstitution := by
  intro i n p ν
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact atom_substitution i n a ν
  | negative p ih => exact not_congr ih
  | conjunction p q ihp ihq => exact and_congr ihp ihq
  | disjunction p q ihp ihq => exact or_congr ihp ihq

theorem row_variables_substitution (i n : Nat) (row : Row) (v : Nat) :
    v ∈ rowVariables (rowSubstitute i n row) ↔ v ≠ i ∧ v ∈ rowVariables row := by
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hsource, hname⟩ := (residual_mem i n row a).mp ha
    exact ⟨hname, List.mem_map.mpr ⟨a, hsource, rfl⟩⟩
  · rintro ⟨hname, hv⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact List.mem_map.mpr ⟨a, (residual_mem i n row a).mpr ⟨ha, hname⟩, rfl⟩

private theorem shared_disjunction (P Q R : Prop) :
    (P ∧ Q) ∨ (P ∧ R) ↔ P ∧ (Q ∨ R) := by
  constructor
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩
  · rintro ⟨hp, hq | hr⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩

theorem exactSubstitutionSupport : BoundedRowsTargets.ExactSubstitutionSupport := by
  intro i n p v
  induction p with
  | truth => simp only [substitute, Formula.variables, List.not_mem_nil, and_false]
  | falsity => simp only [substitute, Formula.variables, List.not_mem_nil, and_false]
  | atom a =>
      cases a with
      | nonnegative row => exact row_variables_substitution i n row v
      | divisible m row => exact row_variables_substitution i n row v
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simp only [substitute, Formula.variables, List.mem_append, ihp, ihq]
      exact shared_disjunction _ _ _
  | disjunction p q ihp ihq =>
      simp only [substitute, Formula.variables, List.mem_append, ihp, ihq]
      exact shared_disjunction _ _ _

theorem any_eval (ps : List Formula) (ν : Nat → Nat) :
    (any ps).eval ν ↔ ∃ p ∈ ps, p.eval ν := by
  induction ps with
  | nil => simp [any, Formula.eval]
  | cons p ps ih =>
      change (p.eval ν ∨ (any ps).eval ν) ↔ ∃ q ∈ p :: ps, q.eval ν
      constructor
      · rintro (hp | hps)
        · exact ⟨p, List.mem_cons_self, hp⟩
        · obtain ⟨q, hq, hv⟩ := ih.mp hps
          exact ⟨q, List.mem_cons_of_mem p hq, hv⟩
      · rintro ⟨q, hq, hv⟩
        rcases List.mem_cons.mp hq with hq | hq
        · subst q
          exact Or.inl hv
        · exact Or.inr (ih.mpr ⟨q, hq, hv⟩)

theorem any_variables (ps : List Formula) (v : Nat) :
    v ∈ (any ps).variables ↔ ∃ p ∈ ps, v ∈ p.variables := by
  induction ps with
  | nil => simp [any, Formula.variables]
  | cons p ps ih =>
      change v ∈ p.variables ++ (any ps).variables ↔ ∃ q ∈ p :: ps, v ∈ q.variables
      rw [List.mem_append]
      constructor
      · rintro (hp | hps)
        · exact ⟨p, List.mem_cons_self, hp⟩
        · obtain ⟨q, hq, hv⟩ := ih.mp hps
          exact ⟨q, List.mem_cons_of_mem p hq, hv⟩
      · rintro ⟨q, hq, hv⟩
        rcases List.mem_cons.mp hq with hq | hq
        · subst q
          exact Or.inl hv
        · exact Or.inr (ih.mpr ⟨q, hq, hv⟩)

theorem actualBoundedElimination : BoundedRowsTargets.ActualBoundedElimination := by
  intro i bound p ν
  rw [bounded, any_eval]
  constructor
  · rintro ⟨q, hq, hv⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
    exact ⟨n, List.mem_range.mp hn, (actualFormulaSubstitution i n p ν).mp hv⟩
  · rintro ⟨n, hn, hv⟩
    exact ⟨substitute i n p, List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩,
      (actualFormulaSubstitution i n p ν).mpr hv⟩

theorem exactBoundedSupport : BoundedRowsTargets.ExactBoundedSupport := by
  intro i bound p v
  rw [bounded, any_variables]
  constructor
  · rintro ⟨q, hq, hv⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
    have hb := List.mem_range.mp hn
    exact ⟨by omega, (exactSubstitutionSupport i n p v).mp hv⟩
  · rintro ⟨hb, hname, hv⟩
    exact ⟨substitute i 0 p, List.mem_map.mpr ⟨0, List.mem_range.mpr hb, rfl⟩,
      (exactSubstitutionSupport i 0 p v).mpr ⟨hname, hv⟩⟩

theorem actualBlockElimination : BoundedRowsTargets.ActualBlockElimination := by
  intro bounds p ν
  induction bounds generalizing ν with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨i, bound⟩
      change (bounded i bound (block rest p)).eval ν ↔
        ∃ n : Nat, n < bound ∧ boundedPrefix (Function.update ν i n) rest p
      rw [actualBoundedElimination i bound (block rest p) ν]
      exact exists_congr (fun n => and_congr Iff.rfl (ih (Function.update ν i n)))

theorem exactBlockSupport : BoundedRowsTargets.ExactBlockSupport := by
  intro bounds p v
  induction bounds with
  | nil => simp [block]
  | cons entry rest ih =>
      rcases entry with ⟨i, bound⟩
      change v ∈ (bounded i bound (block rest p)).variables ↔ _
      rw [exactBoundedSupport i bound (block rest p) v, ih]
      simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, not_or]
      constructor
      · rintro ⟨hb, hname, hpositive, hrest, hv⟩
        exact ⟨⟨hb, hpositive⟩, ⟨hname, hrest⟩, hv⟩
      · rintro ⟨⟨hb, hpositive⟩, ⟨hname, hrest⟩, hv⟩
        exact ⟨hb, hname, hpositive, hrest, hv⟩

theorem boundRow_eval (i bound : Nat) (ν : Nat → Nat) :
    (Atom.nonnegative (boundRow i bound)).eval ν ↔ ν i < bound := by
  simp only [Atom.eval, boundRow, rowValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Summand.term, Term.value, neg_one_mul, add_zero]
  omega

theorem boundsFormula_eval (bounds : List (Nat × Nat)) (ν : Nat → Nat) :
    (boundsFormula bounds).eval ν ↔ ∀ entry ∈ bounds, ν entry.1 < entry.2 := by
  induction bounds with
  | nil => simp [boundsFormula, Formula.eval]
  | cons entry rest ih =>
      change ((Atom.nonnegative (boundRow entry.1 entry.2)).eval ν ∧
        (boundsFormula rest).eval ν) ↔ _
      simp only [boundRow_eval, ih, List.mem_cons, forall_eq_or_imp]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof
