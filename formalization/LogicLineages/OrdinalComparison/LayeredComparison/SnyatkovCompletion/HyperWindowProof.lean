module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowProof
open HyperWindow

private theorem value_calibration (i : Nat) (e h : Int) (ν : Nat → Nat) :
    (valueTerm i e h).value ν =
      SnyatkovHyperCollision.translatedValue ((indexTerm i e).value ν) h := by
  simp only [valueTerm, innerTerm, Term.value, WindowProof.shifted_value,
    SnyatkovHyperCollision.translatedValue, SnyatkovHyperCollision.shiftedInput]

private theorem index_value (i : Nat) (e : Int) (ν : Nat → Nat) :
    (indexTerm i e).value ν = ((ν i : Int) + e).toNat :=
  WindowProof.shifted_value (.variable i) e ν

private theorem index_domains (i j : Nat) (e h k l : Int) (c : Nat) (ν : Nat → Nat)
    (hp : (HyperWindow.closeMatrix i j e h k l c).eval ν) :
    0 ≤ (ν i : Int) + e ∧ 0 ≤ (ν j : Int) + k := by
  have hi : (-e).toNat ≤ ν i := Nat.le_of_not_gt hp.1.1
  have hj : (-k).toNat ≤ ν j := Nat.le_of_not_gt hp.2.1.1
  constructor <;> omega

private theorem raw_bound (n B : Nat) (e : Int)
    (hb : ((n : Int) + e).toNat < B) : n < B + e.natAbs + 1 := by
  have he := Int.le_natAbs (a := -e)
  simp only [Int.natAbs_neg] at he
  omega

theorem actualCollisionAlternatives : HyperWindowTargets.ActualCollisionAlternatives := by
  intro i j e h k l c ν hp
  have hlo0 : (valueTerm j k l).value ν ≤ (valueTerm i e h).value ν :=
    Nat.le_of_not_gt hp.2.2.1
  have hhi0 : (valueTerm i e h).value ν ≤ c * (valueTerm j k l).value ν :=
    Nat.le_of_not_gt hp.2.2.2
  have hlo : SnyatkovHyperCollision.translatedValue ((indexTerm j k).value ν) l ≤
      SnyatkovHyperCollision.translatedValue ((indexTerm i e).value ν) h := by
    simpa only [value_calibration] using hlo0
  have hhi : SnyatkovHyperCollision.translatedValue ((indexTerm i e).value ν) h ≤
      c * SnyatkovHyperCollision.translatedValue ((indexTerm j k).value ν) l := by
    simpa only [value_calibration] using hhi0
  rcases lt_trichotomy ((indexTerm i e).value ν) ((indexTerm j k).value ν) with ht | heq | ht
  · have hb := SnyatkovHyperCollision.Proof.finiteWindowAndDomains.1 1 l h
      ((indexTerm j k).value ν) ((indexTerm i e).value ν) ht (by simpa only [one_mul] using hlo)
    rw [index_value] at hb
    exact Or.inl (raw_bound (ν i) _ e hb)
  · exact Or.inr (Or.inr heq)
  · have hb := SnyatkovHyperCollision.Proof.finiteWindowAndDomains.1 c h l
      ((indexTerm i e).value ν) ((indexTerm j k).value ν) ht hhi
    rw [index_value] at hb
    exact Or.inr (Or.inl (raw_bound (ν j) _ k hb))

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

private theorem equality_replacement (i j : Nat) (hij : i ≠ j)
    (e h k l : Int) (c x y : Nat) (ν : Nat → Nat)
    (hp : (HyperWindow.closeMatrix i j e h k l c).eval
      (Function.update (Function.update ν i x) j y))
    (heq : (indexTerm i e).value (Function.update (Function.update ν i x) j y) =
      (indexTerm j k).value (Function.update (Function.update ν i x) j y)) :
    (shiftTerm (.variable j) (k - e)).value (Function.update ν j y) = x := by
  have hd := index_domains i j e h k l c _ hp
  simp only [Function.update_self, Function.update_of_ne hij] at hd
  simp only [index_value, Function.update_self, Function.update_of_ne hij] at heq
  rw [WindowProof.shifted_value]
  simp only [Term.value, Function.update_self]
  omega

theorem actualTwoVariableElimination : HyperWindowTargets.ActualTwoVariableElimination := by
  intro i j hij e h k l c p ν
  constructor
  · rintro ⟨x, y, hp, hmat⟩
    have halt := actualCollisionAlternatives i j e h k l c
      (Function.update (Function.update ν i x) j y) hp
    simp only [Function.update_self, Function.update_of_ne hij] at halt
    rcases halt with hx | hy | heq
    · apply Or.inl
      refine ⟨y, (bounded_truth _ i _ _).mpr ⟨x, hx, ?_⟩⟩
      rw [← Function.update_comm hij x y ν]
      exact ⟨hp, hmat⟩
    · refine Or.inr (Or.inl ?_)
      exact ⟨x, (bounded_truth _ j _ _).mpr ⟨y, hy, ⟨hp, hmat⟩⟩⟩
    · refine Or.inr (Or.inr ?_)
      refine ⟨y, (WindowProof.matrix_substitution _ _ _ _).mpr ?_⟩
      have hr := equality_replacement i j hij e h k l c x y ν hp heq
      rw [hr, ← Function.update_comm hij x y ν]
      exact ⟨heq, hp, hmat⟩
  · rintro (⟨y, hleft⟩ | ⟨x, hright⟩ | ⟨y, hequal⟩)
    · obtain ⟨x, hx, hp⟩ := (bounded_truth _ i _ _).mp hleft
      rw [← Function.update_comm hij x y ν] at hp
      exact ⟨x, y, hp.1, hp.2⟩
    · obtain ⟨y, hy, hp⟩ := (bounded_truth _ j _ _).mp hright
      exact ⟨x, y, hp.1, hp.2⟩
    · have hp := (WindowProof.matrix_substitution _ _ _ _).mp hequal
      let x := (shiftTerm (.variable j) (k - e)).value (Function.update ν j y)
      change (Matrix.conjunction _ _).eval (Function.update (Function.update ν j y) i x) at hp
      rw [← Function.update_comm hij x y ν] at hp
      exact ⟨x, y, hp.2.1, hp.2.2⟩

private theorem close_support (i j v : Nat) (e h k l : Int) (c : Nat) :
    v ∈ (HyperWindow.closeMatrix i j e h k l c).variables → v = i ∨ v = j := by
  simp only [HyperWindow.closeMatrix, domainMatrix, valueTerm, innerTerm, indexTerm,
    shiftDomain, shiftTerm, atMost, Matrix.variables, Term.variables,
    List.mem_append, List.mem_singleton, List.not_mem_nil]
  tauto

private theorem bounded_support (p : Matrix) (i B v : Nat)
    (hv : v ∈ (Matrix.any ((List.range B).map
      (fun n => p.substitute i (.numeral n)))).variables) :
    v ≠ i ∧ v ∈ p.variables := by
  obtain ⟨q, hq, hv⟩ := (WindowProof.any_support _ v).mp hv
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hq
  have hs := (WindowProof.matrix_support p (.numeral n) i v).mp hv
  simpa only [Term.variables, List.not_mem_nil, and_false, false_and, or_false, and_comm] using hs

theorem exactSupportReduction : HyperWindowTargets.ExactSupportReduction := by
  intro i j hij e h k l c p v
  refine ⟨?_, ?_, ?_⟩
  · intro hv
    obtain ⟨hne, hs⟩ := bounded_support _ i _ v hv
    rcases List.mem_append.mp hs with hc | hp
    · rcases close_support i j v e h k l c hc with he | he
      · exact False.elim (hne he)
      · exact ⟨hne, Or.inl he⟩
    · exact ⟨hne, Or.inr hp⟩
  · intro hv
    obtain ⟨hne, hs⟩ := bounded_support _ j _ v hv
    rcases List.mem_append.mp hs with hc | hp
    · rcases close_support i j v e h k l c hc with he | he
      · exact ⟨hne, Or.inl he⟩
      · exact False.elim (hne he)
    · exact ⟨hne, Or.inr hp⟩
  · intro hv
    have hs := (WindowProof.matrix_support _ (shiftTerm (.variable j) (k - e)) i v).mp hv
    rcases hs with ⟨hs, hne⟩ | ⟨_, hr⟩
    · rcases List.mem_append.mp hs with heq | hrest
      · have he : v = i ∨ v = j := by
          simpa [Matrix.variables, indexTerm, shiftTerm, Term.variables] using heq
        rcases he with he | he
        · exact False.elim (hne he)
        · exact ⟨hne, Or.inl he⟩
      · rcases List.mem_append.mp hrest with hc | hp
        · rcases close_support i j v e h k l c hc with he | he
          · exact False.elim (hne he)
          · exact ⟨hne, Or.inl he⟩
        · exact ⟨hne, Or.inr hp⟩
    · have he : v = j := by simpa [shiftTerm, Term.variables] using hr
      exact ⟨by intro hi; exact hij (hi.symm.trans he), Or.inl he⟩

theorem actualBoundPrograms : HyperWindowTargets.ActualBoundPrograms := by
  have habs := IntegerAlgorithms.Proof.abs_primitive
  constructor
  · let P := Int × (Int × Int)
    have he : Primrec (fun p : P => p.1.natAbs) := habs.comp Primrec.fst
    have hh : Primrec (fun p : P => p.2.1.natAbs) := habs.comp (Primrec.fst.comp Primrec.snd)
    have hl : Primrec (fun p : P => p.2.2.natAbs) := habs.comp (Primrec.snd.comp Primrec.snd)
    exact Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 1) hl) hh)
          (Primrec.const 1)) he) (Primrec.const 1)
  · let P := Int × (Int × (Int × Nat))
    have hh : Primrec (fun p : P => p.1.natAbs) := habs.comp Primrec.fst
    have hk : Primrec (fun p : P => p.2.1.natAbs) := habs.comp (Primrec.fst.comp Primrec.snd)
    have hl : Primrec (fun p : P => p.2.2.1.natAbs) :=
      habs.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have hc : Primrec (fun p : P => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.nat_add.comp hc hh) hl) (Primrec.const 1)) hk)
      (Primrec.const 1)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowProof
