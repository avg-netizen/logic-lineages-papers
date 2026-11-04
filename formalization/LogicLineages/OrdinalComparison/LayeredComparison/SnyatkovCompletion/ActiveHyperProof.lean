module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperProof

private theorem phi_linear (n : Nat) : 2 * n ≤ Phi n := by
  calc
    2 * n ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (Nat.lt_two_pow_self.le)
    _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ 2 ^ (n + 100) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ Phi n := two_pow_shift_le_Phi n

private theorem hyper_linear (n : Nat) : 2 * n ≤ FixedSeedControlResidue.H n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    calc
      2 * (n + 1) ≤ 2 * FixedSeedControlResidue.H n :=
        Nat.mul_le_mul_left 2 (FixedSeedControlResidue.Proof.h_lower_bound n)
      _ ≤ Phi (FixedSeedControlResidue.H n) := phi_linear _
      _ = FixedSeedControlResidue.H (n + 1) := (FixedSeedControlResidue.Proof.h_succ n).symm

private theorem shift_lower (n : Nat) (e : Int) : n ≤ ((n : Int) + e).toNat + e.natAbs := by
  have he := Int.le_natAbs (a := -e)
  simp only [Int.natAbs_neg] at he
  omega

private theorem shift_upper (n : Nat) (e : Int) : ((n : Int) + e).toNat ≤ n + e.natAbs := by
  have he := Int.le_natAbs (a := e)
  omega

theorem actualCoefficientCollisionBound : ActiveHyperTargets.ActualCoefficientCollisionBound := by
  intro e h k a n hp
  have hc : SnyatkovHyperCollision.shiftedInput (((n : Int) + e).toNat) h ≤
      ((n : Int) + k).toNat + a :=
    SnyatkovHyperCollision.Proof.actualCoefficientElimination _ _ a hp
  have he := shift_lower n e
  have hH := hyper_linear (((n : Int) + e).toNat)
  have hh := shift_lower (FixedSeedControlResidue.H (((n : Int) + e).toNat)) h
  have hk := shift_upper n k
  unfold SnyatkovHyperCollision.shiftedInput at hc
  unfold ActiveHyper.bound
  omega

private theorem hyper_value (j : Nat) (e h : Int) (ν : Nat → Nat) :
    (HyperWindow.valueTerm j e h).value ν =
      SnyatkovHyperCollision.translatedValue (((ν j : Int) + e).toNat) h := by
  simp only [HyperWindow.valueTerm, HyperWindow.innerTerm, HyperWindow.indexTerm,
    Term.value, WindowProof.shifted_value, SnyatkovHyperCollision.translatedValue,
    SnyatkovHyperCollision.shiftedInput]

private theorem plain_value (j : Nat) (e : Int) (ν : Nat → Nat) :
    (Term.phi (shiftTerm (.variable j) e)).value ν = Phi (((ν j : Int) + e).toNat) := by
  rw [Term.value, WindowProof.shifted_value]
  rfl

theorem actualGuardBound : ActiveHyperTargets.ActualGuardBound := by
  intro i j kind e h k l q a ν hp
  have hlo : (HyperWindow.valueTerm j k l).value ν ≤
      (LinearWindow.valueTerm i kind e h).value ν := Nat.le_of_not_gt hp.2.2.2.1
  have hhi : (LinearWindow.valueTerm i kind e h).value ν ≤
      a * (Term.phi (shiftTerm (.variable j) q)).value ν := Nat.le_of_not_gt hp.2.2.2.2
  have hc := hlo.trans hhi
  rw [hyper_value, plain_value] at hc
  exact actualCoefficientCollisionBound k l q a (ν j) hc

private theorem bounded_truth (p : Matrix) (i B : Nat) (ν : Nat → Nat) :
    (Matrix.any ((List.range B).map (fun n => p.substitute i (.numeral n)))).eval ν ↔
      ∃ n : Nat, n < B ∧ p.eval (Function.update ν i n) := by
  rw [WindowProof.any_truth]
  constructor
  · rintro ⟨q, hq, hp⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
    exact ⟨n, List.mem_range.mp hn, (WindowProof.matrix_substitution _ _ _ _).mp hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨_, List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩,
      (WindowProof.matrix_substitution _ _ _ _).mpr hp⟩

theorem actualFiniteElimination : ActiveHyperTargets.ActualFiniteElimination := by
  intro i j kind e h k l q a p ν
  constructor
  · rintro ⟨n, hg, hp⟩
    apply (bounded_truth _ j _ ν).mpr
    have hn := actualGuardBound i j kind e h k l q a (Function.update ν j n) hg
    exact ⟨n, by simpa only [Function.update_self] using hn, ⟨hg, hp⟩⟩
  · intro hp
    obtain ⟨n, hn, hp⟩ := (bounded_truth _ j _ ν).mp hp
    exact ⟨n, hp.1, hp.2⟩

private theorem guard_support (i j v : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) :
    v ∈ (ActiveHyper.guard i j kind e h k l q a).variables → v = i ∨ v = j := by
  cases kind <;>
    simp [ActiveHyper.guard, LinearWindow.domainMatrix, LinearWindow.valueTerm,
      HyperWindow.domainMatrix, HyperWindow.valueTerm, HyperWindow.innerTerm,
      HyperWindow.indexTerm, shiftDomain, shiftTerm, atMost, Matrix.variables, Term.variables]
  all_goals tauto

theorem exactSupportReduction : ActiveHyperTargets.ExactSupportReduction := by
  intro i j kind e h k l q a p v hv
  rw [ActiveHyper.finiteCases, WindowProof.any_support] at hv
  obtain ⟨r, hr, hv⟩ := hv
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
  have hs := (WindowProof.matrix_support
    (Matrix.conjunction (ActiveHyper.guard i j kind e h k l q a) p) (.numeral n) j v).mp hv
  have hpair : v ≠ j ∧ v ∈ (Matrix.conjunction
      (ActiveHyper.guard i j kind e h k l q a) p).variables := by
    simpa only [Term.variables, List.not_mem_nil, and_false, false_and, or_false, and_comm] using hs
  rcases List.mem_append.mp hpair.2 with hg | hp
  · rcases guard_support i j v kind e h k l q a hg with he | he
    · exact ⟨hpair.1, Or.inl he⟩
    · exact False.elim (hpair.1 he)
  · exact ⟨hpair.1, Or.inr hp⟩

theorem actualBoundProgram : ActiveHyperTargets.ActualBoundProgram := by
  let P := Int × (Int × (Int × Nat))
  have he : Primrec (fun p : P => p.1.natAbs) := IntegerAlgorithms.Proof.abs_primitive.comp Primrec.fst
  have hh : Primrec (fun p : P => p.2.1.natAbs) :=
    IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.fst.comp Primrec.snd)
  have hk : Primrec (fun p : P => p.2.2.1.natAbs) :=
    IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have ha : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp ha (Primrec.nat_mul.comp (Primrec.const 2) he)) hh) hk)
    (Primrec.const 1)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperProof
