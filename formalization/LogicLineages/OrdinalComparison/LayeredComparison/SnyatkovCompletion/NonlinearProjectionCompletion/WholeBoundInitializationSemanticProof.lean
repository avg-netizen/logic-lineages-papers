module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsEmbeddingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
open WholeBoundInitialization

theorem entries_value (bound : List Nat) (positive negative : Term)
    (es : List (Int × NormalForm.Summand)) (ν : Nat → Nat) :
    BlockRows.rowValue (entries bound positive negative es) ν =
      (positive.value ν : Int) - (negative.value ν : Int) +
        (es.map (fun a => a.1 * (a.2.term.value ν : Int))).sum := by
  induction es with
  | nil => rfl
  | cons a es ih =>
      by_cases h : bound.contains a.2.name = true
      · simp only [entries, if_pos h, BlockRows.rowValue, List.map_cons, List.sum_cons]
        simp only [BlockRows.rowValue] at ih
        omega
      · have hw : (a.1.toNat : Int) * (a.2.term.value ν : Int) -
            ((-a.1).toNat : Int) * (a.2.term.value ν : Int) =
            a.1 * (a.2.term.value ν : Int) := by
          rw [← sub_mul]
          have hc : (a.1.toNat : Int) - ((-a.1).toNat : Int) = a.1 := by omega
          rw [hc]
        simp only [entries, if_neg h, BlockRows.rowValue, Term.value,
          Int.natCast_add, Int.natCast_mul, List.map_cons, List.sum_cons]
        simp only [BlockRows.rowValue] at ih
        omega

theorem literalRowSemantics : WholeBoundInitializationTargets.LiteralRowSemantics := by
  intro bound r ν
  rw [row, entries_value]
  have hc : (r.1.toNat : Int) - ((-r.1).toNat : Int) = r.1 := by omega
  simpa only [Term.value, hc, NormalForm.rowValue]

theorem atom_semantics (bound : List Nat) (a : NormalForm.Atom) (ν : Nat → Nat) :
    (atom bound a).eval ν ↔ a.eval ν := by
  cases a <;> simp only [atom, BlockRows.Atom.eval, NormalForm.Atom.eval,
    literalRowSemantics bound _ ν]

theorem actualFormulaSemantics : WholeBoundInitializationTargets.ActualFormulaSemantics := by
  intro bound p ν
  induction p <;> simp_all only [«initialize», BlockRows.Formula.eval,
    NormalForm.Formula.eval, atom_semantics]

theorem prefix_semantics (bound names : List Nat) (p : NormalForm.Formula) (ν : Nat → Nat) :
    PlainBlockSplit.existsPrefix ν names («initialize» bound p) ↔
      NormalForm.existsPrefix ν names p := by
  induction names generalizing ν with
  | nil => exact actualFormulaSemantics bound p ν
  | cons i names ih =>
      change (∃ n : Nat, PlainBlockSplit.existsPrefix (Function.update ν i n) names
        («initialize» bound p)) ↔
        ∃ n : Nat, NormalForm.existsPrefix (Function.update ν i n) names p
      exact exists_congr (fun n => ih (Function.update ν i n))

theorem exactPrefixSemantics : WholeBoundInitializationTargets.ExactPrefixSemantics :=
  fun bound p ν => prefix_semantics bound bound p ν

#print axioms entries_value
#print axioms literalRowSemantics
#print axioms atom_semantics
#print axioms actualFormulaSemantics
#print axioms prefix_semantics
#print axioms exactPrefixSemantics
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
