module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsProof
open BlockRows

theorem actualOriginalRowEmbedding : BlockRowsTargets.ActualOriginalRowEmbedding := by
  intro r ν
  simp only [Row.ofOriginal, rowValue, NormalForm.rowValue, Term.value]
  have hc : (r.1.toNat : Int) - ((-r.1).toNat : Int) = r.1 := by omega
  rw [hc]

private theorem original_atom (a : NormalForm.Atom) (ν : Nat → Nat) :
    (Atom.ofOriginal a).eval ν ↔ a.eval ν := by
  cases a with
  | nonnegative r =>
    simp only [Atom.ofOriginal, Atom.eval, NormalForm.Atom.eval]
    rw [actualOriginalRowEmbedding r ν]
  | divisible m r =>
    simp only [Atom.ofOriginal, Atom.eval, NormalForm.Atom.eval]
    rw [actualOriginalRowEmbedding r ν]

theorem actualOriginalFormulaEmbedding : BlockRowsTargets.ActualOriginalFormulaEmbedding := by
  intro p ν
  induction p <;>
    simp_all only [Formula.ofOriginal, Formula.eval, NormalForm.Formula.eval, original_atom]

private theorem original_parameters (p : NormalForm.Formula) :
    (Formula.ofOriginal p).parameters = [] := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simpa only [Formula.ofOriginal, Formula.parameters, ihp, ihq, List.nil_append]
  | disjunction p q ihp ihq =>
    simpa only [Formula.ofOriginal, Formula.parameters, ihp, ihq, List.nil_append]

theorem actualInitialBlockIndependence : BlockRowsTargets.ActualInitialBlockIndependence := by
  intro bound p i hi
  rw [original_parameters]
  exact List.not_mem_nil

private theorem weighted_decomposition (entries : List (Int × NormalForm.Summand)) (ν : Nat → Nat) :
    (entries.map (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      ((entries.foldr (fun a rest => Term.add (Term.multiply a.1.toNat a.2.term) rest)
        (.numeral 0)).value ν : Int) -
      ((entries.foldr (fun a rest => Term.add (Term.multiply (-a.1).toNat a.2.term) rest)
        (.numeral 0)).value ν : Int) := by
  have h := NormalFormSemanticProof.actualSignedRowDecomposition ((0 : Int), entries) ν
  simpa [NormalForm.rowValue, NormalForm.positiveTerm, NormalForm.negativeTerm, Term.value] using h

theorem row_decomposition (r : Row) (ν : Nat → Nat) :
    rowValue r ν = ((positiveTerm r).value ν : Int) - ((negativeTerm r).value ν : Int) := by
  have h := weighted_decomposition r.2 ν
  simp only [rowValue, positiveTerm, negativeTerm, Term.value, Int.natCast_add]
  omega

private theorem absolute_value (r : Row) (ν : Nat → Nat) :
    (absoluteTerm r).value ν = (rowValue r ν).natAbs := by
  rw [row_decomposition]
  simp only [absoluteTerm, Term.value]
  omega

private theorem atom_compilation (a : Atom) (ν : Nat → Nat) :
    a.compile.eval ν ↔ a.eval ν := by
  cases a with
  | nonnegative r =>
    simp only [Atom.compile, atMost, Matrix.eval, Atom.eval, row_decomposition]
    omega
  | divisible m r =>
    simp only [Atom.compile, Matrix.eval, Atom.eval, absolute_value]
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

theorem actualExpandedCompilation : BlockRowsTargets.ActualExpandedCompilation := by
  intro p ν
  induction p <;>
    simp_all only [Formula.compile, Matrix.eval, Formula.eval, atom_compilation]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsProof
