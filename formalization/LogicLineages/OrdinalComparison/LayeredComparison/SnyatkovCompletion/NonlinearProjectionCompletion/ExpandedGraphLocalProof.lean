module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph NormalForm

theorem equation_eval (r : NormalForm.Row) (ν : Nat → Nat) :
    (ExpandedGraph.equation r).eval ν ↔ rowValue r ν = 0 :=
  SourceTermGraphSemanticProof.equation_eval r ν

theorem literalSubtraction : ExpandedGraphTargets.LiteralSubtraction := by
  intro z x y ν
  simp only [subtraction, NormalForm.Formula.eval, nonnegative, NormalForm.Atom.eval,
    equation_eval, rowValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Summand.term, Term.value, one_mul, neg_one_mul, add_zero, zero_add]
  omega

theorem literalDivision : ExpandedGraphTargets.LiteralDivision := by
  intro z x c ν
  by_cases hc : c = 0
  · simp only [division, if_pos hc, equation_eval, rowValue, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Summand.term, Term.value, one_mul, add_zero, zero_add]
    subst c
    omega
  · have hpos : 0 < c := Nat.pos_of_ne_zero hc
    have harith : (division z x c).eval ν ↔
        c * ν z ≤ ν x ∧ ν x < c * ν z + c := by
      simp only [division, if_neg hc, NormalForm.Formula.eval, nonnegative, NormalForm.Atom.eval,
        rowValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Summand.term, Term.value, one_mul, neg_one_mul, neg_mul, add_zero, zero_add,
        ← Int.natCast_mul]
      omega
    have hdiv := Nat.div_eq_iff (x := ν x) (y := ν z) hpos
    rw [Nat.mul_comm (ν z) c] at hdiv
    rw [harith]
    constructor
    · rintro ⟨hlo, hhi⟩
      exact (hdiv.mpr ⟨hlo, by omega⟩).symm
    · intro h
      have hh := hdiv.mp h.symm
      exact ⟨hh.1, by omega⟩

theorem literalInverse : ExpandedGraphTargets.LiteralInverse := by
  intro u z x ν
  have harith : (inverse u z x).eval ν ↔
      ν u = ν z + 1 ∧ (ν z = 0 ∨ Phi (ν z) ≤ ν x) ∧ ν x < Phi (ν u) := by
    simp only [inverse, NormalForm.Formula.eval, nonnegative, NormalForm.Atom.eval,
      equation_eval, rowValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Summand.term, shiftTerm, Term.value, Int.toNat_zero, neg_zero, Nat.sub_zero,
      one_mul, neg_one_mul, add_zero, zero_add]
    omega
  have hf := SnyatkovInverse.Proof.exactOriginalGraphs.1 (ν x) (ν z)
  rw [harith]
  constructor
  · rintro ⟨hu, hlo, hhi⟩
    refine ⟨hu, (hf.mpr ⟨hlo, ?_⟩).symm⟩
    simpa only [hu] using hhi
  · rintro ⟨hu, hz⟩
    have hh := hf.mp hz.symm
    exact ⟨hu, hh.1, by simpa only [hu] using hh.2⟩

#print axioms equation_eval
#print axioms literalSubtraction
#print axioms literalDivision
#print axioms literalInverse

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
