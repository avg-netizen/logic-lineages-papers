module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowProof
open LinearWindow

private def argument (kind : Bool) (e h : Int) (n : Nat) : Nat :=
  if kind then ((FixedSeedControlResidue.H (((n : Int) + e).toNat) : Int) + h).toNat
  else ((n : Int) + e).toNat

private theorem value_calibration (i : Nat) (kind : Bool) (e h : Int) (ν : Nat → Nat) :
    (LinearWindow.valueTerm i kind e h).value ν = Phi (argument kind e h (ν i)) := by
  cases kind <;> simp [LinearWindow.valueTerm, argument, HyperWindow.valueTerm,
    HyperWindow.innerTerm, HyperWindow.indexTerm, Term.value, WindowProof.shifted_value]

private theorem shift_lower (n : Nat) (e : Int) : n ≤ ((n : Int) + e).toNat + e.natAbs := by
  have he := Int.le_natAbs (a := -e)
  simp only [Int.natAbs_neg] at he
  omega

private theorem argument_lower (kind : Bool) (e h : Int) (n : Nat) :
    n ≤ argument kind e h n + shiftBudget kind e h := by
  have he := shift_lower n e
  cases kind with
  | false => simpa [argument, shiftBudget] using he
  | true =>
    have hh := FixedSeedControlResidue.Proof.h_lower_bound (((n : Int) + e).toNat)
    have hs := shift_lower (FixedSeedControlResidue.H (((n : Int) + e).toNat)) h
    simp only [argument, shiftBudget, ↓reduceIte]
    omega

private theorem phi_quadratic (n : Nat) : n * (n + 1) ≤ Phi n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hl : n + 1 ≤ Phi n := self_lt_Phi n
    calc
      (n + 1) * (n + 1 + 1) = (n + 2) * (n + 1) := Nat.mul_comm _ _
      _ ≤ (n + 2) * Phi n := Nat.mul_le_mul_left _ hl
      _ ≤ Phi (n + 1) := fullFastControlHierarchyGrowth.2.2 n n le_rfl

private theorem bounded_argument (a n t E : Nat) (hn : n ≤ t + E)
    (hp : Phi t ≤ a * n) : n < a + a * E + E + 1 := by
  by_contra hlarge
  have ht : a + a * E + 1 ≤ t := by omega
  have ha : a ≤ t := by omega
  have he : a * E < t := by omega
  have hupper : a * n ≤ a * t + a * E := by
    calc
      a * n ≤ a * (t + E) := Nat.mul_le_mul_left a hn
      _ = a * t + a * E := Nat.mul_add _ _ _
  have hstrict : a * t + a * E < t * t + t :=
    Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right t ha) he
  have hquad : t * t + t ≤ Phi t := by
    simpa only [Nat.mul_add, Nat.mul_one] using phi_quadratic t
  have hbad := (hupper.trans_lt hstrict).trans_le hquad
  omega

theorem actualNonlinearLinearBound : LinearWindowTargets.ActualNonlinearLinearBound := by
  intro kind e h a n hp
  have hp' : Phi (argument kind e h n) ≤ a * n := by
    simpa only [value_calibration] using hp
  exact bounded_argument a n (argument kind e h n) (shiftBudget kind e h)
    (argument_lower kind e h n) hp'

theorem actualGuardBound : LinearWindowTargets.ActualGuardBound := by
  intro i j leftKind rightKind e h k l a ν hp
  have hlo : (LinearWindow.valueTerm j rightKind k l).value ν ≤
      (LinearWindow.valueTerm i leftKind e h).value ν := Nat.le_of_not_gt hp.2.2.1
  have hhi : (LinearWindow.valueTerm i leftKind e h).value ν ≤ a * ν j :=
    Nat.le_of_not_gt hp.2.2.2
  have hcal : (LinearWindow.valueTerm j rightKind k l).value ν =
      (LinearWindow.valueTerm 0 rightKind k l).value (fun _ => ν j) := by
    rw [value_calibration, value_calibration]
  exact actualNonlinearLinearBound rightKind k l a (ν j) (by rw [← hcal]; exact hlo.trans hhi)

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

theorem actualFiniteElimination : LinearWindowTargets.ActualFiniteElimination := by
  intro i j hij leftKind rightKind e h k l a p ν
  constructor
  · rintro ⟨n, hg, hp⟩
    apply (bounded_truth _ j _ ν).mpr
    have hn := actualGuardBound i j leftKind rightKind e h k l a (Function.update ν j n) hg
    exact ⟨n, by simpa only [Function.update_self] using hn, ⟨hg, hp⟩⟩
  · intro hout
    obtain ⟨n, hn, hp⟩ := (bounded_truth _ j _ ν).mp hout
    exact ⟨n, hp.1, hp.2⟩

private theorem value_support (i v : Nat) (kind : Bool) (e h : Int) :
    v ∈ (LinearWindow.valueTerm i kind e h).variables ↔ v = i := by
  cases kind <;> simp [LinearWindow.valueTerm, HyperWindow.valueTerm, HyperWindow.innerTerm,
    HyperWindow.indexTerm, shiftTerm, Term.variables]

private theorem domain_support (i v : Nat) (kind : Bool) (e h : Int) :
    v ∈ (LinearWindow.domainMatrix i kind e h).variables ↔ v = i := by
  cases kind <;> simp [LinearWindow.domainMatrix, HyperWindow.domainMatrix,
    HyperWindow.indexTerm, shiftDomain, shiftTerm, Matrix.variables, Term.variables]

private theorem guard_support (i j v : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) :
    v ∈ (LinearWindow.guard i j leftKind rightKind e h k l a).variables → v = i ∨ v = j := by
  simp only [LinearWindow.guard, atMost, Matrix.variables, Term.variables,
    List.mem_append, List.mem_singleton, value_support, domain_support]
  tauto

theorem exactSupportReduction : LinearWindowTargets.ExactSupportReduction := by
  intro i j hij leftKind rightKind e h k l a p v hv
  rw [LinearWindow.finiteCases, WindowProof.any_support] at hv
  obtain ⟨q, hq, hv⟩ := hv
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
  have hs := (WindowProof.matrix_support
    (Matrix.conjunction (LinearWindow.guard i j leftKind rightKind e h k l a) p)
    (.numeral n) j v).mp hv
  have hpair : v ≠ j ∧ v ∈ (Matrix.conjunction
      (LinearWindow.guard i j leftKind rightKind e h k l a) p).variables := by
    simpa only [Term.variables, List.not_mem_nil, and_false, false_and, or_false, and_comm] using hs
  rcases List.mem_append.mp hpair.2 with hg | hp
  · rcases guard_support i j v leftKind rightKind e h k l a hg with he | he
    · exact ⟨hpair.1, Or.inl he⟩
    · exact False.elim (hpair.1 he)
  · exact ⟨hpair.1, Or.inr hp⟩

theorem actualBoundProgram : LinearWindowTargets.ActualBoundProgram := by
  let P := Bool × (Int × (Int × Nat))
  have he : Primrec (fun p : P => p.2.1.natAbs) :=
    IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.fst.comp Primrec.snd)
  have hh : Primrec (fun p : P => p.2.2.1.natAbs) :=
    IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have ha : Primrec (fun p : P => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hB : Primrec (fun p : P => shiftBudget p.1 p.2.1 p.2.2.1) :=
    Primrec.nat_add.comp he
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) hh (Primrec.const 0))
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp ha (Primrec.nat_mul.comp ha hB)) hB)
    (Primrec.const 1)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowProof
