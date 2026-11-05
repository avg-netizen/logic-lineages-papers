module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsSemanticProof
open NormalForm NestedRows

theorem replacement_high (j : Nat) (a b : Int) (ν : Nat → Nat)
    (ha : 0 ≤ (ν j : Int) + a) :
    replacement j a b ν = SignedRows.replacement j (a + b) ν := by
  unfold replacement SignedRows.replacement
  rw [Int.toNat_of_nonneg ha, add_assoc]

theorem replacement_low (j : Nat) (a b : Int) (ν : Nat → Nat)
    (ha : ¬ 0 ≤ (ν j : Int) + a) :
    replacement j a b ν = b.toNat := by
  have hz : ((ν j : Int) + a).toNat = 0 := by omega
  unfold replacement
  simp only [hz, Int.natCast_zero, zero_add]

theorem actualNestedSubstitution : NestedRowsTargets.ActualNestedSubstitution := by
  intro i j a b p ν
  change (((SignedRows.anchorDomain j a).eval ν ∧
      (SignedRows.substitute i j (a + b) p).eval ν) ∨
    (¬ (SignedRows.anchorDomain j a).eval ν ∧
      (BoundedRows.substitute i b.toNat p).eval ν)) ↔ _
  simp only [SignedRowsSemanticProof.anchorDomain_eval]
  by_cases ha : 0 ≤ (ν j : Int) + a
  · simp only [ha, true_and, not_true_eq_false, false_and, or_false]
    rw [replacement_high j a b ν ha]
    exact SignedRowsSemanticProof.actualTotalSubstitution i j (a + b) p ν
  · simp only [ha, false_and, not_false_eq_true, true_and, false_or]
    rw [replacement_low j a b ν ha]
    exact BoundedRowsSemanticProof.actualFormulaSubstitution i b.toNat p ν

theorem exactNestedSupport : NestedRowsTargets.ExactNestedSupport := by
  intro i j a b p v
  change v ∈ (((SignedRows.anchorDomain j a).variables ++
      (SignedRows.substitute i j (a + b) p).variables) ++
    ((SignedRows.anchorDomain j a).variables ++
      (BoundedRows.substitute i b.toNat p).variables)) ↔ _
  simp only [List.mem_append, SignedRowsSemanticProof.anchorDomain_variables,
    SignedRowsSemanticProof.exactTotalSupport i j (a + b) p v,
    BoundedRowsSemanticProof.exactSubstitutionSupport i b.toNat p v]
  tauto

theorem actualGuardedAtomSubstitution : NestedRowsTargets.ActualGuardedAtomSubstitution := by
  intro i j a b atom ν
  rw [actualNestedSubstitution i j a b (guardedAtom atom) ν]
  change ((domainFormula atom.row).eval (Function.update ν i (replacement j a b ν)) ∧
      atom.eval (Function.update ν i (replacement j a b ν))) ↔ _
  rw [NormalFormSemanticProof.exactOriginalRowDomains atom.row
    (Function.update ν i (replacement j a b ν))]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsSemanticProof
