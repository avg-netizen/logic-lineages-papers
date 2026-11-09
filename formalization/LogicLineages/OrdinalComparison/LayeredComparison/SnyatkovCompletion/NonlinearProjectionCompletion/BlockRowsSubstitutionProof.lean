module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsEmbeddingProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsProof
open BlockRows

theorem original_summand_variables (s : NormalForm.Summand) (j : Nat) :
    j ∈ s.term.variables ↔ j = s.name := by
  cases s <;> simp [NormalForm.Summand.term, NormalForm.Summand.name,
    HyperWindow.valueTerm, HyperWindow.innerTerm, HyperWindow.indexTerm, shiftTerm, Term.variables]

theorem moved_summand_variables (s : NormalForm.Summand) (i : Nat) (replacement : Term)
    (hs : s.name = i) (j : Nat) :
    j ∈ (s.term.substitute i replacement).variables ↔ j ∈ replacement.variables := by
  rw [WindowProof.term_support]
  simp [original_summand_variables, hs]

private theorem unchanged_summand (s : NormalForm.Summand) (i : Nat) (replacement : Term)
    (ν : Nat → Nat) (hs : s.name ≠ i) :
    s.term.value (Function.update ν i (replacement.value ν)) = s.term.value ν := by
  apply WindowProof.term_update s.term i (replacement.value ν) ν
  intro h
  exact hs ((original_summand_variables s i).mp h).symm

private theorem entries_value (i : Nat) (replacement positive negative : Term)
    (entries : List (Int × NormalForm.Summand)) (ν : Nat → Nat) :
    rowValue (substituteEntries i replacement positive negative entries) ν =
      (positive.value ν : Int) - (negative.value ν : Int) +
        (entries.map (fun a => a.1 *
          (a.2.term.value (Function.update ν i (replacement.value ν)) : Int))).sum := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    by_cases hs : a.2.name = i
    · have ht := WindowProof.term_substitution a.2.term replacement i ν
      have hw : (a.1.toNat : Int) *
          (a.2.term.value (Function.update ν i (replacement.value ν)) : Int) -
          ((-a.1).toNat : Int) *
          (a.2.term.value (Function.update ν i (replacement.value ν)) : Int) =
          a.1 * (a.2.term.value (Function.update ν i (replacement.value ν)) : Int) := by
        rw [← sub_mul]
        have hc : (a.1.toNat : Int) - ((-a.1).toNat : Int) = a.1 := by omega
        rw [hc]
      simp only [substituteEntries, if_pos hs, rowValue, Term.value,
        Int.natCast_add, Int.natCast_mul, ht, List.map_cons, List.sum_cons]
      simp only [rowValue] at ih
      omega
    · have ht := unchanged_summand a.2 i replacement ν hs
      simp only [substituteEntries, if_neg hs, rowValue, List.map_cons, List.sum_cons, ht]
      simp only [rowValue] at ih
      omega

theorem row_substitution (r : Row) (i : Nat) (replacement : Term) (ν : Nat → Nat) :
    rowValue (r.substitute i replacement) ν =
      rowValue r (Function.update ν i (replacement.value ν)) := by
  rw [Row.substitute, entries_value]
  simp only [WindowProof.term_substitution, rowValue]

private theorem atom_substitution (a : Atom) (i : Nat) (replacement : Term) (ν : Nat → Nat) :
    (a.substitute i replacement).eval ν ↔ a.eval (Function.update ν i (replacement.value ν)) := by
  cases a <;> simp only [Atom.substitute, Atom.eval, row_substitution]

theorem formula_substitution (p : Formula) (i : Nat) (replacement : Term) (ν : Nat → Nat) :
    (p.substitute i replacement).eval ν ↔ p.eval (Function.update ν i (replacement.value ν)) := by
  induction p <;>
    simp_all only [Formula.substitute, Formula.eval, atom_substitution]

theorem actualSourceSubstitution : BlockRowsTargets.ActualSourceSubstitution :=
  ⟨row_substitution, formula_substitution⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsProof
