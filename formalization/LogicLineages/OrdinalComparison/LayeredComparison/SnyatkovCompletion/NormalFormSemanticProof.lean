module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormSemanticProof
open NormalForm

/-- The least hyper-index includes the exceptional range below H(0)=1. -/
theorem hyperThreshold_exact (h : Int) (j : Nat) :
    hyperThreshold h ≤ j ↔ hyperRequired h ≤ FixedSeedControlResidue.H j := by
  by_cases hh : hyperRequired h ≤ 1
  · have hj := FixedSeedControlResidue.Proof.h_lower_bound j
    simp only [hyperThreshold, hh, ↓reduceIte, Nat.zero_le, true_iff]
    omega
  · simp only [hyperThreshold, hh, ↓reduceIte]
    by_cases hj : j = 0
    · subst j
      rw [FixedSeedControlResidue.Proof.h_zero]
      omega
    · rcases SnyatkovInverse.Proof.originalOrderAndRoundTrips with
        ⟨_, _, _, _, _, _, horder⟩
      have ht := (horder (hyperRequired h - 1) j (by omega)).2.2.1
      omega

theorem exactOriginalDomainCutoffs : NormalFormTargets.ExactOriginalDomainCutoffs := by
  intro s ν
  cases s with
  | «variable» i => simp [Summand.meaningful, Summand.domainCutoff]
  | phi i e =>
      simp only [Summand.meaningful, Summand.domainCutoff, Summand.name]
      omega
  | hyperPhi i e h =>
      simp only [Summand.meaningful, Summand.domainCutoff, Summand.name]
      have ht := hyperThreshold_exact h (((ν i : Int) + e).toNat)
      have hreq : hyperRequired h ≤ FixedSeedControlResidue.H (((ν i : Int) + e).toNat) ↔
          0 ≤ (FixedSeedControlResidue.H (((ν i : Int) + e).toNat) : Int) + h := by
        unfold hyperRequired
        omega
      rw [hreq] at ht
      constructor
      · rintro ⟨hi, ho⟩
        have hbound := ht.mpr ho
        omega
      · intro hbound
        have hi : 0 ≤ (ν i : Int) + e := by omega
        refine ⟨hi, ht.mp ?_⟩
        omega

private theorem split_int (z : Int) :
    z = (z.toNat : Int) - ((-z).toNat : Int) := by omega

private theorem row_tail_decomposition (xs : List (Int × Summand)) (ν : Nat → Nat) :
    (xs.map (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      ((xs.foldr (fun a rest => Term.add (Term.multiply a.1.toNat a.2.term) rest)
        (Term.numeral 0)).value ν : Int) -
      ((xs.foldr (fun a rest => Term.add (Term.multiply (-a.1).toNat a.2.term) rest)
        (Term.numeral 0)).value ν : Int) := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, List.foldr_nil, Term.value, Int.natCast_zero, sub_self]
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.foldr_cons, Term.value,
        Int.natCast_add, Int.natCast_mul]
      rw [ih]
      have ha := split_int a.1
      calc
        _ = ((a.1.toNat : Int) - ((-a.1).toNat : Int)) * (a.2.term.value ν : Int) +
            (((xs.foldr (fun a rest => Term.add (Term.multiply a.1.toNat a.2.term) rest)
              (Term.numeral 0)).value ν : Int) -
             ((xs.foldr (fun a rest => Term.add (Term.multiply (-a.1).toNat a.2.term) rest)
              (Term.numeral 0)).value ν : Int)) := by rw [← ha]
        _ = _ := by rw [sub_mul]; omega

theorem actualSignedRowDecomposition : NormalFormTargets.ActualSignedRowDecomposition := by
  intro row ν
  simp only [rowValue, positiveTerm, negativeTerm, Term.value, Int.natCast_add]
  rw [row_tail_decomposition]
  have h := split_int row.1
  omega

private theorem domain_atom (s : Summand) (ν : Nat → Nat) :
    (Atom.nonnegative (domainRow s)).eval ν ↔ s.meaningful ν := by
  rw [exactOriginalDomainCutoffs]
  simp only [Atom.eval, rowValue, domainRow, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Summand.term, Term.value, one_mul, add_zero]
  omega

private theorem domain_list (xs : List (Int × Summand)) (ν : Nat → Nat) :
    (xs.foldr (fun a rest => Formula.conjunction
      (.atom (.nonnegative (domainRow a.2))) rest) .truth).eval ν ↔
      ∀ a ∈ xs, a.2.meaningful ν := by
  induction xs with
  | nil => simp [List.foldr_nil, Formula.eval]
  | cons a xs ih =>
      simp only [List.foldr_cons, Formula.eval, domain_atom, ih,
        List.mem_cons, forall_eq_or_imp]

theorem exactOriginalRowDomains : NormalFormTargets.ExactOriginalRowDomains := by
  intro row ν
  exact domain_list row.2 ν

private theorem absolute_value (row : Row) (ν : Nat → Nat) :
    (absoluteTerm row).value ν = (rowValue row ν).natAbs := by
  rw [actualSignedRowDecomposition row ν]
  simp only [absoluteTerm, Term.value]
  omega

theorem actualAtomCompilation : NormalFormTargets.ActualAtomCompilation := by
  intro a ν
  cases a with
  | nonnegative row =>
      simp only [Atom.compile, atMost, Matrix.eval, Atom.eval,
        actualSignedRowDecomposition row ν]
      omega
  | divisible m row =>
      simp only [Atom.compile, Matrix.eval, Atom.eval, absolute_value]
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

theorem actualBooleanCompilation : NormalFormTargets.ActualBooleanCompilation := by
  intro p ν
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact actualAtomCompilation a ν
  | negative p ih => simpa only [Formula.compile, Matrix.eval, Formula.eval] using not_congr ih
  | conjunction p q ihp ihq =>
      simpa only [Formula.compile, Matrix.eval, Formula.eval] using and_congr ihp ihq
  | disjunction p q ihp ihq =>
      simpa only [Formula.compile, Matrix.eval, Formula.eval] using or_congr ihp ihq

private theorem summand_variables (s : Summand) : s.term.variables = [s.name] := by
  cases s <;>
    simp only [Summand.term, Summand.name, HyperWindow.valueTerm, HyperWindow.innerTerm,
      HyperWindow.indexTerm, shiftTerm, Term.variables, List.append_nil]

private theorem tail_variables (xs : List (Int × Summand)) (negative : Bool) :
    (xs.foldr (fun a rest => Term.add
      (.multiply (if negative then (-a.1).toNat else a.1.toNat) a.2.term) rest)
      (.numeral 0)).variables = xs.map (fun a => a.2.name) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.foldr_cons, Term.variables, summand_variables, ih,
        List.singleton_append, List.map_cons]

private theorem positive_variables (row : Row) :
    (positiveTerm row).variables = rowVariables row := by
  simpa only [positiveTerm, Term.variables, List.nil_append, rowVariables,
    Bool.false_eq_true, ↓reduceIte] using tail_variables row.2 false

private theorem negative_variables (row : Row) :
    (negativeTerm row).variables = rowVariables row := by
  simpa only [negativeTerm, Term.variables, List.nil_append, rowVariables,
    ↓reduceIte] using tail_variables row.2 true

private theorem atom_variables (a : Atom) (i : Nat) :
    i ∈ a.compile.variables ↔ i ∈ rowVariables a.row := by
  cases a <;> simp only [Atom.compile, Atom.row, atMost, absoluteTerm,
    Matrix.variables, Term.variables, positive_variables, negative_variables,
    List.mem_append, or_self]

theorem exactVariableMembership : NormalFormTargets.ExactVariableMembership := by
  intro p i
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact atom_variables a i
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simpa only [Formula.compile, Formula.variables, Matrix.variables, List.mem_append]
        using or_congr ihp ihq
  | disjunction p q ihp ihq =>
      simpa only [Formula.compile, Formula.variables, Matrix.variables, List.mem_append]
        using or_congr ihp ihq

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormSemanticProof
