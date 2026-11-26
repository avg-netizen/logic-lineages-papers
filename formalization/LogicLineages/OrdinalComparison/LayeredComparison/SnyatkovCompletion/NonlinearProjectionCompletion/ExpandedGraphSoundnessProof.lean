module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphLocalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph NormalForm

theorem multiply_equation (z x c : Nat) (ν : Nat → Nat) :
    (ExpandedGraph.equation (multiplyRow z x c)).eval ν ↔ ν z = c * ν x := by
  rw [equation_eval]
  simp only [multiplyRow, rowValue, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Summand.term, Term.value, one_mul, neg_mul, add_zero, zero_add,
    ← Int.natCast_mul]
  omega

theorem graph_numeral (start n : Nat) (ν : Nat → Nat) :
    (graph start (.numeral n)).eval ν ↔ ν start = n :=
  SourceTermGraphSemanticProof.numeral_equation start n ν

theorem graph_variable (start i : Nat) (ν : Nat → Nat) :
    (graph start (.variable i)).eval ν ↔ ν start = ν i :=
  SourceTermGraphSemanticProof.variable_equation start i ν

theorem graph_add (start : Nat) (a b : Term) (ν : Nat → Nat) :
    (graph start (.add a b)).eval ν ↔
      (graph start a).eval ν ∧ (graph (start + nodeCount a) b).eval ν ∧
      ν (output start (.add a b)) = ν (output start a) + ν (output (start + nodeCount a) b) := by
  change ((graph start a).eval ν ∧ (graph (start + nodeCount a) b).eval ν ∧ _) ↔ _
  rw [ExpandedGraph.equation, SourceTermGraphSemanticProof.addition_equation]

theorem graph_subtract (start : Nat) (a b : Term) (ν : Nat → Nat) :
    (graph start (.subtract a b)).eval ν ↔
      (graph start a).eval ν ∧ (graph (start + nodeCount a) b).eval ν ∧
      ν (output start (.subtract a b)) = ν (output start a) - ν (output (start + nodeCount a) b) := by
  change ((graph start a).eval ν ∧ (graph (start + nodeCount a) b).eval ν ∧ _) ↔ _
  rw [literalSubtraction]

theorem graph_multiply (start : Nat) (c : Nat) (a : Term) (ν : Nat → Nat) :
    (graph start (.multiply c a)).eval ν ↔
      (graph start a).eval ν ∧ ν (output start (.multiply c a)) = c * ν (output start a) := by
  change ((graph start a).eval ν ∧ _) ↔ _
  rw [multiply_equation]

theorem graph_divide (start : Nat) (c : Nat) (a : Term) (ν : Nat → Nat) :
    (graph start (.divide c a)).eval ν ↔
      (graph start a).eval ν ∧ ν (output start (.divide c a)) = ν (output start a) / c := by
  change ((graph start a).eval ν ∧ _) ↔ _
  rw [literalDivision]

theorem graph_phi (start : Nat) (a : Term) (ν : Nat → Nat) :
    (graph start (.phi a)).eval ν ↔
      (graph start a).eval ν ∧ ν (output start (.phi a)) = Phi (ν (output start a)) := by
  change ((graph start a).eval ν ∧ _) ↔ _
  rw [ExpandedGraph.equation, SourceTermGraphSemanticProof.phi_equation]

theorem graph_phiInverse (start : Nat) (a : Term) (ν : Nat → Nat) :
    (graph start (.phiInverse a)).eval ν ↔
      (graph start a).eval ν ∧
      ν (start + nodeCount a) = ν (output start (.phiInverse a)) + 1 ∧
      ν (output start (.phiInverse a)) = SnyatkovInverse.phiInverse (ν (output start a)) := by
  change ((graph start a).eval ν ∧ _) ↔ _
  rw [literalInverse]

theorem graphSoundness : ExpandedGraphTargets.GraphSoundness := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ν hf h
      simpa only [output, nodeCount, Nat.add_sub_cancel, Term.value] using
        (graph_numeral start n ν).mp h
  | «variable» i =>
      intro ν hf h
      simpa only [output, nodeCount, Nat.add_sub_cancel, Term.value] using
        (graph_variable start i ν).mp h
  | add a b iha ihb =>
      intro ν hf h
      have hfa := (Bool.and_eq_true_iff.mp hf).1
      have hfb := (Bool.and_eq_true_iff.mp hf).2
      obtain ⟨ha, hb, hout⟩ := (graph_add start a b ν).mp h
      rw [iha start ν hfa ha, ihb (start + nodeCount a) ν hfb hb] at hout
      exact hout
  | subtract a b iha ihb =>
      intro ν hf h
      have hfa := (Bool.and_eq_true_iff.mp hf).1
      have hfb := (Bool.and_eq_true_iff.mp hf).2
      obtain ⟨ha, hb, hout⟩ := (graph_subtract start a b ν).mp h
      rw [iha start ν hfa ha, ihb (start + nodeCount a) ν hfb hb] at hout
      exact hout
  | multiply c a ih =>
      intro ν hf h
      obtain ⟨ha, hout⟩ := (graph_multiply start c a ν).mp h
      rw [ih start ν hf ha] at hout
      exact hout
  | divide c a ih =>
      intro ν hf h
      obtain ⟨ha, hout⟩ := (graph_divide start c a ν).mp h
      rw [ih start ν hf ha] at hout
      exact hout
  | phi a ih =>
      intro ν hf h
      obtain ⟨ha, hout⟩ := (graph_phi start a ν).mp h
      rw [ih start ν hf ha] at hout
      exact hout
  | phiInverse a ih =>
      intro ν hf h
      obtain ⟨ha, _, hout⟩ := (graph_phiInverse start a ν).mp h
      rw [ih start ν hf ha] at hout
      exact hout
  | hyper a ih => intro ν hf; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at hf
  | hyperInverse a ih => intro ν hf; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at hf

#print axioms multiply_equation
#print axioms graph_numeral
#print axioms graph_variable
#print axioms graph_add
#print axioms graph_subtract
#print axioms graph_multiply
#print axioms graph_divide
#print axioms graph_phi
#print axioms graph_phiInverse
#print axioms graphSoundness
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
