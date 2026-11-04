module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibilityTargets
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueResiduesProof
public import LogicLineages.OrdinalComparison.ControlResidueProof
public import Mathlib.Data.Int.ModEq
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility.Proof
open CommonLayerSyntax FixedSeedControlResidue

private theorem term_residue (p : Parameters) (hm : 0 < p.2.1)
    (n : Nat) (hn : cutoff p ≤ n) :
    Nat.ModEq p.2.1 (termValue p.1 n p.2.2.1) (fastControlResidue p.2.1) := by
  unfold cutoff at hn
  unfold termValue
  split
  · exact phiShiftedConstantResidues _ hm n (by omega)
  · split
    · exact FixedSeedControlResidue.Proof.h_eventual_residue _ hm n (by omega)
    · apply phiShiftedConstantResidues _ hm
      have hg := FixedSeedControlResidue.Proof.h_lower_bound n
      have he := Int.le_natAbs (a := -p.2.2.1)
      simp only [Int.natAbs_neg] at he
      unfold SnyatkovHyperCollision.shiftedInput
      omega

private theorem div_abs (m : Nat) (z : Int) :
    z.natAbs % m = 0 ↔ (m : Int) ∣ z := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

private theorem predicate_tail (p : Parameters) (hm : 0 < p.2.1)
    (n : Nat) (hn : cutoff p ≤ n) : predicate p n = tailBit p := by
  have h := Int.natCast_modEq_iff.mpr (term_residue p hm n hn)
  have hc := (h.mul_left p.2.2.2.1).add_right p.2.2.2.2
  rw [Bool.eq_iff_iff]
  simp only [predicate, tailBit, decide_eq_true_eq]
  exact (div_abs _ _).trans (hc.dvd_iff.trans (div_abs _ _).symm)

private theorem small_lookup (p : Parameters) (n : Nat) (hn : n < cutoff p) :
    (smallBits p).getD n false = predicate p n := by
  simp [smallBits, List.getD_eq_getElem?_getD, hn]

theorem exactFiniteTailElimination : Targets.ExactFiniteTailElimination := by
  intro p hm
  refine ⟨predicate_tail p hm, ?_⟩
  intro n
  by_cases h : n < cutoff p
  · simp only [h, true_and, Nat.not_le.mpr h, false_and, or_false]
    rw [small_lookup p n h]
  · have hn : cutoff p ≤ n := by omega
    simp only [h, false_and, hn, true_and, false_or]
    rw [predicate_tail p hm n hn]

private theorem atom_truth (i : Nat) (p : Parameters) (n : Nat) (ν : Nat → Nat) :
    (smallAtom i p n).eval ν ↔ predicate p n = true ∧ ν i = n := by
  by_cases h : predicate p n = true
  · simp only [smallAtom, h, ↓reduceIte, BaseFormula.Formula.eval,
      BaseTerm.value, true_and]
  · simp only [smallAtom, h, Bool.false_eq_true, ↓reduceIte, BaseFormula.Formula.eval, false_and]

private theorem small_truth (i : Nat) (p : Parameters) (ν : Nat → Nat)
    (xs : List Nat) :
    ((xs.foldr (fun n rest => BaseFormula.Formula.disjunction
      (smallAtom i p n) rest) .falsity).eval ν ↔
      ∃ n ∈ xs, predicate p n = true ∧ ν i = n) := by
  induction xs with
  | nil => simp only [List.foldr_nil, BaseFormula.Formula.eval, List.not_mem_nil,
      false_and, exists_false]
  | cons n xs ih =>
    rw [List.foldr_cons]
    change ((smallAtom i p n).eval ν ∨ _) ↔ _
    rw [atom_truth, ih]
    constructor
    · rintro (h | ⟨m, hm, hp, hv⟩)
      · exact ⟨n, List.mem_cons_self, h⟩
      · exact ⟨m, List.mem_cons_of_mem n hm, hp, hv⟩
    · rintro ⟨m, hm, hp, hv⟩
      rcases List.mem_cons.mp hm with he | hm
      · exact Or.inl ⟨by simpa only [he] using hp, hv.trans he⟩
      · exact Or.inr ⟨m, hm, hp, hv⟩

private theorem small_support (i : Nat) (p : Parameters) (xs : List Nat)
    (j : Nat) : j ∈ (xs.foldr (fun n rest =>
      BaseFormula.Formula.disjunction (smallAtom i p n) rest) .falsity).variables → j = i := by
  induction xs with
  | nil => simp [BaseFormula.Formula.variables]
  | cons n xs ih =>
    cases h : predicate p n
    · simpa [List.foldr_cons, smallAtom, h, BaseFormula.Formula.variables] using ih
    · intro hj
      simp only [List.foldr_cons, smallAtom, h, ↓reduceIte,
        BaseFormula.Formula.variables, BaseTerm.variables, List.append_nil,
        List.mem_append, List.mem_singleton] at hj
      exact hj.elim id ih

theorem literalBaseTruthAndSupport : Targets.LiteralBaseTruthAndSupport := by
  intro i p hm
  refine ⟨?_, ?_⟩
  · intro ν
    have hs : (smallFormula i p).eval ν ↔
        ν i < cutoff p ∧ predicate p (ν i) = true := by
      constructor
      · intro h
        obtain ⟨n, hn, hp, hv⟩ := (small_truth i p ν (List.range (cutoff p))).mp h
        subst n
        exact ⟨List.mem_range.mp hn, hp⟩
      · rintro ⟨hn, hp⟩
        exact (small_truth i p ν (List.range (cutoff p))).mpr
          ⟨ν i, List.mem_range.mpr hn, hp, rfl⟩
    have ht : (if tailBit p then BaseFormula.Formula.truth else .falsity).eval ν ↔
        tailBit p = true := by
      cases hb : tailBit p <;>
        simp only [hb, ↓reduceIte, BaseFormula.Formula.eval, Bool.false_eq_true]
    change (ν i = ν i ∧ ((smallFormula i p).eval ν ∨
      (¬ ν i < cutoff p ∧ _))) ↔ _
    rw [ht, hs]
    simp only [eq_self, true_and]
    by_cases hn : ν i < cutoff p
    · simp only [hn, true_and, not_true_eq_false, false_and, or_false]
    · simp only [hn, false_and, not_false_eq_true, true_and, false_or]
      rw [predicate_tail p hm (ν i) (by omega)]
  · intro j
    constructor
    · intro h
      have hs := small_support i p (List.range (cutoff p)) j
      cases hb : tailBit p <;>
        simp [sourceFormula, BaseFormula.Formula.variables, BaseTerm.variables,
          smallFormula, hb] at h
      all_goals rcases h with h | h | h; exact h; exact hs h; exact h
    · intro h
      subst j
      simp [sourceFormula, BaseFormula.Formula.variables, BaseTerm.variables]

private theorem atom_code (i : Nat) (p : Parameters) (n : Nat) :
    smallAtomCode i p n = (smallAtom i p n).encode := by
  cases h : predicate p n <;>
    simp only [smallAtomCode, smallAtom, h, ↓reduceIte,
      BaseFormula.Formula.encode, BaseFormula.Formula.guardView,
      CommonHeadCompiler.encode, BaseTerm.encode, Bool.false_eq_true]

private theorem small_code (i : Nat) (p : Parameters) :
    smallCode i p = (smallFormula i p).encode := by
  unfold smallCode smallFormula
  generalize List.range (cutoff p) = xs
  induction xs with
  | nil => rfl
  | cons n xs ih =>
    rw [List.foldr_cons, List.foldr_cons]
    change smallAtomCode i p n ++ _ ++ [(7, 0, 0)] =
      (smallAtom i p n).encode ++ _ ++ [(7, 0, 0)]
    rw [atom_code, ih]
    rfl

theorem exactCodeCalibration : Targets.ExactCodeCalibration := by
  intro i p
  cases h : tailBit p <;>
    simp [formulaCode, sourceFormula, BaseFormula.Formula.encode,
      BaseFormula.Formula.guardView, CommonHeadCompiler.encode,
      BaseTerm.encode, h, small_code, List.append_assoc]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility.Proof
