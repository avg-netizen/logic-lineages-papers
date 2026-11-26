module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
open NormalForm

def zeroSummand : Summand → Bool
  | .variable _ => true
  | .phi _ shift => decide (shift = 0)
  | .hyperPhi _ _ _ => false
def zeroRow (r : Row) : Bool := r.2.all (fun e => zeroSummand e.2)
def zeroFormula (p : NormalForm.Formula) : Bool :=
  (LinearRows.atoms p).all (fun a => zeroRow a.row)

theorem equation_zero (r : Row) :
    zeroFormula (ExpandedGraph.equation r) = zeroRow r := by
  simp [zeroFormula, zeroRow, LinearRows.atoms, ExpandedGraph.equation,
    SourceTermGraph.equation, SourceTermGraph.negateRow, Atom.row, List.all_map]

theorem conjunction_zero (p q : NormalForm.Formula) :
    zeroFormula (.conjunction p q) = (zeroFormula p && zeroFormula q) := by
  simp only [zeroFormula, LinearRows.atoms, List.all_append]

theorem subtraction_zero (z x y : Nat) : zeroFormula (ExpandedGraph.subtraction z x y) = true := by
  simp [ExpandedGraph.subtraction, ExpandedGraph.nonnegative, ExpandedGraph.equation,
    SourceTermGraph.equation, SourceTermGraph.negateRow, zeroFormula, zeroRow,
    zeroSummand, LinearRows.atoms, Atom.row]

theorem division_zero (z x c : Nat) : zeroFormula (ExpandedGraph.division z x c) = true := by
  by_cases hc : c = 0 <;>
    simp [ExpandedGraph.division, hc, ExpandedGraph.nonnegative, ExpandedGraph.equation,
      SourceTermGraph.equation, SourceTermGraph.negateRow, zeroFormula, zeroRow,
      zeroSummand, LinearRows.atoms, Atom.row]

theorem inverse_zero (u z x : Nat) : zeroFormula (ExpandedGraph.inverse u z x) = true := by
  simp [ExpandedGraph.inverse, ExpandedGraph.nonnegative, ExpandedGraph.equation,
    SourceTermGraph.equation, SourceTermGraph.negateRow, zeroFormula, zeroRow,
    zeroSummand, LinearRows.atoms, Atom.row]

/-- This syntactic upper class holds even for unsupported H, whose graph is
literal falsity. It does not assert semantic correctness for those inputs. -/
theorem graph_zero (s : Nat) (t : Term) : zeroFormula (ExpandedGraph.graph s t) = true := by
  open ExpandedGraph in
  induction t generalizing s with
  | numeral n => rw [graph, equation_zero]; rfl
  | «variable» i => rw [graph, equation_zero]; rfl
  | add a b iha ihb =>
      rw [graph, conjunction_zero, conjunction_zero, iha s,
        ihb (s + nodeCount a), equation_zero]
      rfl
  | subtract a b iha ihb =>
      rw [graph, conjunction_zero, conjunction_zero, iha s,
        ihb (s + nodeCount a), subtraction_zero]
      rfl
  | multiply c a ih => rw [graph, conjunction_zero, ih s, equation_zero]; rfl
  | divide c a ih => rw [graph, conjunction_zero, ih s, division_zero]; rfl
  | phi a ih => rw [graph, conjunction_zero, ih s, equation_zero]; rfl
  | phiInverse a ih => rw [graph, conjunction_zero, ih s, inverse_zero]; rfl
  | hyper a ih => rfl
  | hyperInverse a ih => rfl

theorem relation_zero (strict : Bool) (x y : Nat) :
    zeroFormula (SourceRows.relation strict x y) = true := by
  cases strict <;> simp [SourceRows.relation, SourceRows.strictRow,
    SourceTermGraph.equation, SourceTermGraph.negateRow, SourceTermGraph.variableRow,
    zeroFormula, zeroRow, zeroSummand, LinearRows.atoms, Atom.row]

theorem predicate_zero (p : Matrix) (s : Nat) :
    zeroFormula (ExpandedBooleanGraph.predicate s p) = true := by
  open ExpandedBooleanGraph in
  induction p generalizing s with
  | truth => rfl
  | falsity => rfl
  | equal a b => exact relation_zero false _ _
  | less a b => exact relation_zero true _ _
  | divisible m a =>
      by_cases hm : m = 0
      · rw [predicate, if_pos hm, equation_zero]; rfl
      · simp [predicate, hm, zeroFormula, zeroRow, zeroSummand, LinearRows.atoms, Atom.row]
  | negative p ih => exact ih s
  | conjunction p q ihp ihq =>
      rw [predicate, conjunction_zero, ihp s, ihq (s + ExpandedGraph.nodeCount (forest p))]
      rfl
  | disjunction p q ihp ihq =>
      have hp := ihp s
      have hq := ihq (s + ExpandedGraph.nodeCount (forest p))
      simpa only [predicate, zeroFormula, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨hp, hq⟩

theorem literalZeroShiftGraphClass : ExpandedBooleanGraphTargets.LiteralZeroShiftGraphClass := by
  intro bound p hp a ha entry he
  have hz : zeroFormula (ExpandedBooleanGraph.compile bound p) = true := by
    rw [ExpandedBooleanGraph.compile, ExpandedBooleanGraph.matrix, conjunction_zero,
      graph_zero, predicate_zero]
    rfl
  have hrow := List.all_eq_true.mp hz a ha
  have hs := List.all_eq_true.mp hrow entry he
  rcases entry with ⟨c, s⟩
  cases s with
  | «variable» i => exact Or.inl ⟨i, rfl⟩
  | phi i shift =>
      have hshift : shift = 0 := by simpa only [zeroSummand, decide_eq_true_eq] using hs
      subst shift
      exact Or.inr ⟨i, rfl⟩
  | hyperPhi i e h => cases hs

#print axioms zeroSummand
#print axioms zeroRow
#print axioms zeroFormula
#print axioms equation_zero
#print axioms conjunction_zero
#print axioms subtraction_zero
#print axioms division_zero
#print axioms inverse_zero
#print axioms graph_zero
#print axioms relation_zero
#print axioms predicate_zero
#print axioms literalZeroShiftGraphClass
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
