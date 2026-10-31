module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnitTargets
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.Ring.Divisibility.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Proof
open CotreePresburgerLinear CotreePresburgerLinear.Proof

@[simp] theorem eval_map {A B : Type} (p : Boolean A) (f : A → B) (g : B → Bool) :
    (p.map f).eval g = p.eval (g ∘ f) := by
  induction p <;> simp_all [Boolean.map, Boolean.eval]

theorem eval_congr {A : Type} (p : Boolean A) (f g : A → Bool) :
    (∀ a ∈ p.atoms, f a = g a) → p.eval f = p.eval g := by
  induction p with
  | bot => intro _; rfl
  | top => intro _; rfl
  | atom a => intro h; exact h a (by simp [Boolean.atoms])
  | neg p ih =>
    intro h
    simp only [Boolean.eval]
    rw [ih h]
  | conj p q hp hq =>
    intro h
    simp only [Boolean.eval]
    rw [hp (fun a ha => h a (by simp [Boolean.atoms, ha])),
      hq (fun a ha => h a (by simp [Boolean.atoms, ha]))]
  | disj p q hp hq =>
    intro h
    simp only [Boolean.eval]
    rw [hp (fun a ha => h a (by simp [Boolean.atoms, ha])),
      hq (fun a ha => h a (by simp [Boolean.atoms, ha]))]

@[simp] theorem eval_disjoin {A : Type} (xs : List (Boolean A)) (f : A → Bool) :
    (Boolean.disjoin xs).eval f = true ↔ ∃ p ∈ xs, p.eval f = true := by
  induction xs with
  | nil => simp [Boolean.disjoin, Boolean.eval]
  | cons p xs ih =>
    change (p.eval f || (Boolean.disjoin xs).eval f) = true ↔ _
    simp [ih]

theorem list_prod_positive (xs : List Nat) : (∀ a ∈ xs, 0 < a) → 0 < xs.prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro h
    exact Nat.mul_pos (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem periodPositive : Targets.PeriodPositive := by
  intro n u
  apply list_prod_positive
  intro a ha
  rcases List.mem_map.mp ha with ⟨b,_,rfl⟩
  cases b <;> simp [UnitAtom.period]

theorem atom_period_dvd {n : Nat} (u : UnitFormula n) (a : UnitAtom n)
    (ha : a ∈ u.atoms) : a.period ∣ period u :=
  List.dvd_prod (List.mem_map.mpr ⟨a,ha,rfl⟩)

@[simp] theorem subst_atom_eval {n : Nat} (a : UnitAtom n) (b : Affine n) (v : Fin n → Int) :
    Atom.eval v (a.subst b) = UnitAtom.eval v (b.eval v) a := by
  cases a <;> simp [UnitAtom.subst, Atom.eval, UnitAtom.eval]

theorem instantiationExact : Targets.InstantiationExact := by
  intro n u b v
  simp [evalQF, instantiate, evalUnit, Function.comp_def]

@[simp] theorem eval_guarded {n : Nat} (u : UnitFormula n) (v : Fin n → Int) (x : Int) :
    evalUnit (guarded u) v x = true ↔ 0 ≤ x ∧ evalUnit u v x = true := by
  simp [guarded, evalUnit, Boolean.eval, UnitAtom.eval, Sign.value]

@[simp] theorem instantiate_eval {n : Nat} (u : UnitFormula n) (b : Affine n) (v : Fin n → Int) :
    (instantiate u b).eval (Atom.eval v) = evalUnit u v (b.eval v) :=
  instantiationExact n u b v

theorem eliminate_iff {n : Nat} (u : UnitFormula n) (v : Fin n → Int) :
    evalQF (eliminate u) v = true ↔
      ∃ b ∈ cutoffs u, ∃ j : Nat, j < period u ∧
        evalUnit (guarded u) v (b.eval v + (j : Int)) = true := by
  simp [eliminate, evalQF, List.mem_flatMap, List.mem_map]

theorem cutoff_mem {n : Nat} (u : UnitFormula n) (a : UnitAtom n) (ha : a ∈ u.atoms)
    (b : Affine n) (hb : b ∈ a.cutoffs) : b ∈ cutoffs u := by
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a,ha,hb⟩)

/-- Atomwise invariance under movement within the same cutpoint cell and
within the same congruence class. No monotonicity/NNF restriction is assumed. -/
theorem eval_same_cell {n : Nat} (u : UnitFormula n) (v : Fin n → Int) (y z : Int)
    (hcell : ∀ b ∈ cutoffs u, b.eval v ≤ y ↔ b.eval v ≤ z)
    (hperiod : (period u : Int) ∣ y - z) : evalUnit u v y = evalUnit u v z := by
  apply eval_congr
  intro a ha
  cases a with
  | nonneg s t =>
    cases s with
    | zero => simp [UnitAtom.eval, Sign.value]
    | pos =>
      have hc := hcell (Affine.scale (-1) t)
        (cutoff_mem u (.nonneg .pos t) ha _ (by simp [UnitAtom.cutoffs]))
      simp only [eval_scale, neg_one_mul] at hc
      simp only [UnitAtom.eval, Sign.value, one_mul, decide_eq_decide]
      omega
    | neg =>
      have hc := hcell (Affine.add t (Affine.const 1))
        (cutoff_mem u (.nonneg .neg t) ha _ (by simp [UnitAtom.cutoffs]))
      simp only [eval_add, eval_const] at hc
      simp only [UnitAtom.eval, Sign.value, neg_one_mul, decide_eq_decide]
      omega
  | dvd m s t =>
    have hd : (m + 1) ∣ period u := atom_period_dvd u (.dvd m s t) ha
    have hdiff : ((m + 1 : Nat) : Int) ∣ y - z :=
      (Int.natCast_dvd_natCast.mpr hd).trans hperiod
    have hscaled : ((m + 1 : Nat) : Int) ∣ s.value * (y - z) :=
      dvd_mul_of_dvd_right hdiff s.value
    have hterms : ((m + 1 : Nat) : Int) ∣
        (s.value * y + t.eval v) - (s.value * z + t.eval v) := by
      simpa only [mul_sub, add_sub_add_right_eq_sub] using hscaled
    exact decide_eq_decide.mpr (dvd_iff_dvd_of_dvd_sub hterms)

/-- An actual largest evaluated cutpoint below a nonnegative witness exists
because zero belongs to the finite list. This is only a proof selection;
the executable elimination enumerates every syntactic cutpoint. -/
theorem largest_cutoff {n : Nat} (u : UnitFormula n) (v : Fin n → Int) (y : Int) (hy : 0 ≤ y) :
    ∃ b ∈ cutoffs u, b.eval v ≤ y ∧
      ∀ c ∈ cutoffs u, c.eval v ≤ y → c.eval v ≤ b.eval v := by
  let s : Finset Int := ((cutoffs u).map (fun b => b.eval v)).toFinset.filter (fun z => z ≤ y)
  have hzero : (0 : Int) ∈ (cutoffs u).map (fun b => b.eval v) :=
    List.mem_map.mpr ⟨Affine.const 0, by simp [cutoffs], by simp⟩
  have hs : s.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hzero,hy⟩⟩
  have hm := Finset.max'_mem s hs
  have hmf := Finset.mem_filter.mp hm
  rcases List.mem_map.mp (List.mem_toFinset.mp hmf.1) with ⟨b,hb,hbeq⟩
  refine ⟨b,hb,?_,?_⟩
  · rw [hbeq]; exact hmf.2
  · intro c hc hcy
    rw [hbeq]
    exact Finset.le_max' s _ (Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨c,hc,rfl⟩),hcy⟩)

theorem unitEliminationExact : Targets.UnitEliminationExact := by
  intro n u v
  rw [eliminate_iff]
  constructor
  · rintro ⟨b,hb,j,hj,h⟩
    rcases (eval_guarded u v _).mp h with ⟨hpos,hu⟩
    refine ⟨(b.eval v + (j : Int)).toNat, ?_⟩
    simpa only [Int.toNat_of_nonneg hpos] using hu
  · rintro ⟨x,hx⟩
    let y : Int := x
    have hy : 0 ≤ y := Int.natCast_nonneg x
    obtain ⟨b,hb,hby,hmax⟩ := largest_cutoff u v y hy
    have hbzero : 0 ≤ b.eval v := by
      have h := hmax (Affine.const 0) (by simp [cutoffs]) (by simpa using hy)
      simpa using h
    let j : Nat := (y - b.eval v).toNat % period u
    have hjlt : j < period u := Nat.mod_lt _ (periodPositive n u)
    have hjle : j ≤ (y - b.eval v).toNat := Nat.mod_le _ _
    have hdiff : ((y - b.eval v).toNat : Int) = y - b.eval v :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hby)
    have hzle : b.eval v + (j : Int) ≤ y := by omega
    have hzpos : 0 ≤ b.eval v + (j : Int) := by omega
    have hjval : (j : Int) = (y - b.eval v) % (period u : Int) := by
      dsimp [j]
      rw [hdiff]
    have hres : (period u : Int) ∣ y - (b.eval v + (j : Int)) := by
      have heq : y - (b.eval v + (j : Int)) =
          (y - b.eval v) - (y - b.eval v) % (period u : Int) := by
        rw [← hjval]
        omega
      rw [heq]
      exact Int.dvd_self_sub_emod
    have hcell : ∀ c ∈ cutoffs u,
        c.eval v ≤ y ↔ c.eval v ≤ b.eval v + (j : Int) := by
      intro c hc
      constructor
      · intro hcy
        have hcb := hmax c hc hcy
        omega
      · intro hcz
        exact hcz.trans hzle
    have heval := eval_same_cell u v y (b.eval v + (j : Int)) hcell hres
    refine ⟨b,hb,j,hjlt,(eval_guarded u v _).mpr ⟨hzpos,?_⟩⟩
    rw [← heval]
    exact hx

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Proof
