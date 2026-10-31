module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlTargets
public import Mathlib.Data.Nat.Log
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.OrdinalComparison.PerturbedControl.Proof

theorem search_primitive : Primrec₂ search := by
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hs : Primrec (fun p : Nat × (Nat × Nat) => p.2.1+1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  have hm : Primrec (fun p : Nat × (Nat × Nat) => p.1 % (2^(p.2.1+1))) :=
    Primrec.nat_mod.comp Primrec.fst (hpow.comp (Primrec.const 2) hs)
  have hb : Primrec (fun p : Nat × (Nat × Nat) =>
      if p.1 % (2^(p.2.1+1))=0 then p.2.1+1 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) hs (Primrec.snd.comp Primrec.snd)
  have hr := Primrec.nat_rec (Primrec.const 0 : Primrec (fun _ : Nat => 0)) hb.to₂
  apply hr.of_eq
  intro n k
  induction k with
  | zero => rfl
  | succ k ih =>
      change (if n % (2^(k+1))=0 then k+1 else Nat.rec 0 _ k)=search n (k+1)
      rw [ih]
      rfl

theorem valuation_primitive : Primrec valuationTwo :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 0) (search_primitive.comp Primrec.id Primrec.id)

theorem search_divides (n k : Nat) : 2^(search n k) ∣ n := by
  induction k with
  | zero => simp [search]
  | succ k ih =>
      by_cases h : n % (2^(k+1))=0
      · rw [search,if_pos h]
        exact Nat.dvd_of_mod_eq_zero h
      · rw [search,if_neg h]
        exact ih

theorem search_max (n k : Nat) : ∀ i : Nat, i≤k → 2^i ∣ n → i≤search n k := by
  induction k with
  | zero => intro i hi _; simpa only [search] using hi
  | succ k ih =>
      intro i hi hd
      by_cases h : n % (2^(k+1))=0
      · rw [search,if_pos h]
        exact hi
      · rw [search,if_neg h]
        apply ih i _ hd
        by_contra hn
        have he : i=k+1 := by omega
        subst i
        exact h (Nat.mod_eq_zero_of_dvd hd)

theorem valuation_exact (n : Nat) (hn : 0<n) :
    2^(valuationTwo n) ∣ n ∧ ¬ 2^(valuationTwo n+1) ∣ n := by
  have hn0 : n≠0 := by omega
  simp only [valuationTwo,if_neg hn0]
  refine ⟨search_divides n n,?_⟩
  intro hd
  have hp : 2^(search n n+1) ≤ n := Nat.le_of_dvd hn hd
  have he : search n n+1 < 2^(search n n+1) := Nat.lt_two_pow_self
  have hm := search_max n n (search n n+1) (by omega) hd
  omega

theorem valuation : Targets.Valuation :=
  ⟨search_primitive,valuation_primitive,rfl,valuation_exact⟩
end LogicLineages.OrdinalComparison.PerturbedControl.Proof
