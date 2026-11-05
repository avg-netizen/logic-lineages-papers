module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
public import Mathlib.Tactic.Tauto

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsSemanticProof
open NormalForm SignedRows

theorem replacement_cast (j : Nat) (d : Int) (ν : Nat → Nat)
    (hd : 0 ≤ (ν j : Int) + d) :
    (replacement j d ν : Int) = (ν j : Int) + d := by
  unfold replacement
  exact Int.toNat_of_nonneg hd

/-- The offset records exactly the translated linear occurrence. The two
nonlinear constructors instead absorb the translation into their index shift. -/
theorem summand_value (i j : Nat) (d : Int) (s : Summand) (ν : Nat → Nat)
    (hd : 0 ≤ (ν j : Int) + d) :
    offset i d s + ((translateSummand i j d s).term.value ν : Int) =
      (s.term.value (Function.update ν i (replacement j d ν)) : Int) := by
  cases s with
  | «variable» k =>
      by_cases hk : k = i
      · subst k
        simp only [offset, translateSummand, Summand.name, ↓reduceIte,
          Summand.term, Term.value, Function.update_self]
        have hr := replacement_cast j d ν hd
        omega
      · simp only [offset, translateSummand, Summand.name, if_neg hk,
          Summand.term, Term.value, Function.update_of_ne hk, zero_add]
  | phi k e =>
      by_cases hk : k = i
      · subst k
        simp only [offset, zero_add, translateSummand, Summand.name, ↓reduceIte,
          Summand.term, Term.value, WindowProof.shifted_value, Function.update_self]
        rw [replacement_cast j d ν hd]
        simp only [add_assoc]
      · simp only [offset, zero_add, translateSummand, Summand.name, if_neg hk,
          Summand.term, Term.value, WindowProof.shifted_value, Function.update_of_ne hk]
  | hyperPhi k e h =>
      by_cases hk : k = i
      · subst k
        simp only [offset, zero_add, translateSummand, Summand.name, ↓reduceIte,
          Summand.term, HyperWindow.valueTerm, HyperWindow.innerTerm,
          HyperWindow.indexTerm, Term.value, WindowProof.shifted_value, Function.update_self]
        rw [replacement_cast j d ν hd]
        simp only [add_assoc]
      · simp only [offset, zero_add, translateSummand, Summand.name, if_neg hk,
          Summand.term, HyperWindow.valueTerm, HyperWindow.innerTerm,
          HyperWindow.indexTerm, Term.value, WindowProof.shifted_value, Function.update_of_ne hk]

theorem translated_sum_value (i j : Nat) (d : Int) (xs : List (Int × Summand))
    (ν : Nat → Nat) (hd : 0 ≤ (ν j : Int) + d) :
    (xs.map (fun a => a.1 * offset i d a.2)).sum +
        ((xs.map (fun a => (a.1, translateSummand i j d a.2))).map
          (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      (xs.map (fun a => a.1 *
        (a.2.term.value (Function.update ν i (replacement j d ν)) : Int))).sum := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, add_zero]
  | cons a xs ih =>
      have ha := summand_value i j d a.2 ν hd
      simp only [List.map_cons, List.sum_cons]
      rw [← ha, mul_add]
      omega

theorem actualRowTranslation : SignedRowsTargets.ActualRowTranslation := by
  intro i j d row ν hd
  have h := translated_sum_value i j d row.2 ν hd
  simp only [rowTranslate, rowValue]
  omega

theorem exactTranslatedOccurrences : SignedRowsTargets.ExactTranslatedOccurrences := by
  intro i j d row
  rfl

theorem summand_meaningful (i j : Nat) (d : Int) (s : Summand) (ν : Nat → Nat)
    (hd : 0 ≤ (ν j : Int) + d) :
    (translateSummand i j d s).meaningful ν ↔
      s.meaningful (Function.update ν i (replacement j d ν)) := by
  cases s with
  | «variable» k =>
      by_cases hk : k = i <;>
        simp only [translateSummand, Summand.name, hk, ↓reduceIte, Summand.meaningful]
  | phi k e =>
      by_cases hk : k = i
      · subst k
        simp only [translateSummand, Summand.name, ↓reduceIte,
          Summand.meaningful, Function.update_self]
        rw [replacement_cast j d ν hd]
        simp only [add_assoc]
      · simp only [translateSummand, Summand.name, if_neg hk,
          Summand.meaningful, Function.update_of_ne hk]
  | hyperPhi k e h =>
      by_cases hk : k = i
      · subst k
        simp only [translateSummand, Summand.name, ↓reduceIte,
          Summand.meaningful, Function.update_self]
        rw [replacement_cast j d ν hd]
        simp only [add_assoc]
      · simp only [translateSummand, Summand.name, if_neg hk,
          Summand.meaningful, Function.update_of_ne hk]

theorem exactTranslatedDomains : SignedRowsTargets.ExactTranslatedDomains := by
  intro i j d row ν hd
  change (∀ a ∈ row.2.map (fun a => (a.1, translateSummand i j d a.2)),
      a.2.meaningful ν) ↔
    ∀ a ∈ row.2, a.2.meaningful (Function.update ν i (replacement j d ν))
  constructor
  · intro h a ha
    apply (summand_meaningful i j d a.2 ν hd).mp
    exact h (a.1, translateSummand i j d a.2) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (summand_meaningful i j d b.2 ν hd).mpr (h b hb)

theorem atom_translation (i j : Nat) (d : Int) (a : Atom) (ν : Nat → Nat)
    (hd : 0 ≤ (ν j : Int) + d) :
    (atomTranslate i j d a).eval ν ↔
      a.eval (Function.update ν i (replacement j d ν)) := by
  cases a with
  | nonnegative row =>
      change (0 ≤ rowValue (rowTranslate i j d row) ν) ↔
        (0 ≤ rowValue row (Function.update ν i (replacement j d ν)))
      rw [actualRowTranslation i j d row ν hd]
  | divisible m row =>
      change (((m + 1 : Nat) : Int) ∣ rowValue (rowTranslate i j d row) ν) ↔
        (((m + 1 : Nat) : Int) ∣ rowValue row (Function.update ν i (replacement j d ν)))
      rw [actualRowTranslation i j d row ν hd]

theorem actualCoreTranslation : SignedRowsTargets.ActualCoreTranslation := by
  intro i j d p ν hd
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact atom_translation i j d a ν hd
  | negative p ih => exact not_congr ih
  | conjunction p q ihp ihq => exact and_congr ihp ihq
  | disjunction p q ihp ihq => exact or_congr ihp ihq

theorem translated_name (i j : Nat) (d : Int) (s : Summand) :
    (translateSummand i j d s).name = if s.name = i then j else s.name := by
  by_cases hs : s.name = i
  · simp only [translateSummand, if_pos hs]
    cases s <;> rfl
  · simp only [translateSummand, if_neg hs]

theorem row_support (i j : Nat) (d : Int) (row : Row) (v : Nat) :
    v ∈ rowVariables (rowTranslate i j d row) ↔
      (v = j ∧ i ∈ rowVariables row) ∨ (v ≠ i ∧ v ∈ rowVariables row) := by
  constructor
  · intro hv
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    change (translateSummand i j d b.2).name = v at he
    rw [translated_name] at he
    by_cases hname : b.2.name = i
    · simp only [if_pos hname] at he
      exact Or.inl ⟨he.symm, List.mem_map.mpr ⟨b, hb, hname⟩⟩
    · simp only [if_neg hname] at he
      exact Or.inr ⟨fun hvi => hname (he.trans hvi), List.mem_map.mpr ⟨b, hb, he⟩⟩
  · rintro (⟨hv, hi⟩ | ⟨hvi, hv⟩)
    · obtain ⟨a, ha, hname⟩ := List.mem_map.mp hi
      refine List.mem_map.mpr ⟨(a.1, translateSummand i j d a.2),
        List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      change (translateSummand i j d a.2).name = v
      rw [translated_name, if_pos hname]
      exact hv.symm
    · obtain ⟨a, ha, hname⟩ := List.mem_map.mp hv
      have hi : a.2.name ≠ i := fun h => hvi (hname.symm.trans h)
      refine List.mem_map.mpr ⟨(a.1, translateSummand i j d a.2),
        List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      change (translateSummand i j d a.2).name = v
      rw [translated_name, if_neg hi]
      exact hname

theorem exactCoreSupport : SignedRowsTargets.ExactCoreSupport := by
  intro i j d p v
  induction p with
  | truth => simp only [core, Formula.variables, List.not_mem_nil, and_false, or_self]
  | falsity => simp only [core, Formula.variables, List.not_mem_nil, and_false, or_self]
  | atom a =>
      cases a with
      | nonnegative row => exact row_support i j d row v
      | divisible m row => exact row_support i j d row v
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simp only [core, Formula.variables, List.mem_append, ihp, ihq]
      tauto
  | disjunction p q ihp ihq =>
      simp only [core, Formula.variables, List.mem_append, ihp, ihq]
      tauto

theorem anchorDomain_eval (j : Nat) (d : Int) (ν : Nat → Nat) :
    (anchorDomain j d).eval ν ↔ 0 ≤ (ν j : Int) + d := by
  simp only [anchorDomain, Formula.eval, Atom.eval, rowValue, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Summand.term, Term.value,
    one_mul, add_zero]
  omega

theorem actualTotalSubstitution : SignedRowsTargets.ActualTotalSubstitution := by
  intro i j d p ν
  simp only [substitute, Formula.eval, anchorDomain_eval]
  by_cases hd : 0 ≤ (ν j : Int) + d
  · simp only [hd, true_and, not_true_eq_false, false_and, or_false]
    exact actualCoreTranslation i j d p ν hd
  · have hz : replacement j d ν = 0 := by
      unfold replacement
      omega
    simp only [hd, false_and, not_false_eq_true, true_and, false_or]
    rw [hz]
    exact BoundedRowsSemanticProof.actualFormulaSubstitution i 0 p ν

theorem anchorDomain_variables (j : Nat) (d : Int) (v : Nat) :
    v ∈ (anchorDomain j d).variables ↔ v = j := by
  simp only [anchorDomain, Formula.variables, Atom.row, rowVariables,
    List.map_cons, List.map_nil, Summand.name, List.mem_cons, List.not_mem_nil, or_false]

theorem exactTotalSupport : SignedRowsTargets.ExactTotalSupport := by
  intro i j d p v
  simp only [substitute, Formula.variables, List.mem_append, anchorDomain_variables,
    exactCoreSupport i j d p v, BoundedRowsSemanticProof.exactSubstitutionSupport i 0 p v]
  tauto

theorem actualGuardedAtomTranslation : SignedRowsTargets.ActualGuardedAtomTranslation := by
  intro i j d a ν
  rw [actualTotalSubstitution i j d (guardedAtom a) ν]
  change ((domainFormula a.row).eval (Function.update ν i (replacement j d ν)) ∧
      a.eval (Function.update ν i (replacement j d ν))) ↔ _
  rw [NormalFormSemanticProof.exactOriginalRowDomains]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsSemanticProof
