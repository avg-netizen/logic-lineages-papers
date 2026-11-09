module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph NormalForm

theorem equation_plain (r : NormalForm.Row) :
    MaximalPlainBranch.isPlain (ExpandedGraph.equation r) = PlainPhiDominance.isPlain r := by
  simp [MaximalPlainBranch.isPlain, LinearRows.atoms, ExpandedGraph.equation,
    SourceTermGraph.equation, Atom.row, PlainPhiDominance.isPlain,
    SourceTermGraph.negateRow, List.all_map]

theorem conjunction_plain (p q : NormalForm.Formula) :
    MaximalPlainBranch.isPlain (.conjunction p q) =
      (MaximalPlainBranch.isPlain p && MaximalPlainBranch.isPlain q) := by
  simp only [MaximalPlainBranch.isPlain, LinearRows.atoms, List.all_append]

theorem subtraction_plain (z x y : Nat) :
    MaximalPlainBranch.isPlain (subtraction z x y) = true := by
  simp [subtraction, nonnegative, ExpandedGraph.equation, SourceTermGraph.equation,
    SourceTermGraph.negateRow, MaximalPlainBranch.isPlain, LinearRows.atoms, Atom.row,
    PlainPhiDominance.isPlain]

theorem division_plain (z x c : Nat) :
    MaximalPlainBranch.isPlain (division z x c) = true := by
  by_cases hc : c = 0 <;>
    simp [division, hc, nonnegative, ExpandedGraph.equation, SourceTermGraph.equation,
      SourceTermGraph.negateRow, MaximalPlainBranch.isPlain, LinearRows.atoms, Atom.row,
      PlainPhiDominance.isPlain]

theorem inverse_plain (u z x : Nat) :
    MaximalPlainBranch.isPlain (inverse u z x) = true := by
  simp [inverse, nonnegative, ExpandedGraph.equation, SourceTermGraph.equation,
    SourceTermGraph.negateRow, MaximalPlainBranch.isPlain, LinearRows.atoms, Atom.row,
    PlainPhiDominance.isPlain]

theorem plainOriginalGraphClass : ExpandedGraphTargets.PlainOriginalGraphClass := by
  intro start t
  induction t generalizing start with
  | numeral n => intro hf; rw [graph, equation_plain]; rfl
  | «variable» i => intro hf; rw [graph, equation_plain]; rfl
  | add a b iha ihb =>
      intro hf
      have ha := (Bool.and_eq_true_iff.mp hf).1
      have hb := (Bool.and_eq_true_iff.mp hf).2
      rw [graph, conjunction_plain, conjunction_plain, iha start ha,
        ihb (start + nodeCount a) hb, equation_plain]
      rfl
  | subtract a b iha ihb =>
      intro hf
      have ha := (Bool.and_eq_true_iff.mp hf).1
      have hb := (Bool.and_eq_true_iff.mp hf).2
      rw [graph, conjunction_plain, conjunction_plain, iha start ha,
        ihb (start + nodeCount a) hb, subtraction_plain]
      rfl
  | multiply c a ih =>
      intro hf
      rw [graph, conjunction_plain, ih start hf, equation_plain]
      rfl
  | divide c a ih =>
      intro hf
      rw [graph, conjunction_plain, ih start hf, division_plain]
      rfl
  | phi a ih =>
      intro hf
      rw [graph, conjunction_plain, ih start hf, equation_plain]
      rfl
  | phiInverse a ih =>
      intro hf
      rw [graph, conjunction_plain, ih start hf, inverse_plain]
      rfl
  | hyper a ih => intro hf; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at hf
  | hyperInverse a ih => intro hf; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at hf

#print axioms equation_plain
#print axioms conjunction_plain
#print axioms subtraction_plain
#print axioms division_plain
#print axioms inverse_plain
#print axioms plainOriginalGraphClass
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
