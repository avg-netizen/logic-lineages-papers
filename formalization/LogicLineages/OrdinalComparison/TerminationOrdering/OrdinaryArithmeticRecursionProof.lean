module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionProof

open FirstOrder Language OrdinaryArithmetic OrdinaryArithmeticRecursionTargets
open OrdinaryArithmeticCompositionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem betaTruth {α : Type} (a b i r : Term α) (v : α → Nat) :
    (betaFormula a b i r).Realize v ↔
    a.realize v % ((i.realize v + 1) * b.realize v + 1) = r.realize v :=
  OrdinaryArithmeticBetaProof.betaTermTruth a b i r v

theorem strictOrderTruth {α : Type} (s t : Term α) (v : α → Nat) :
    (lessFormula s t).Realize v ↔ s.realize v < t.realize v := lessTruth s t v

theorem realize_cons {α : Type} {n : Nat} (t : Term α)
    (ts : Fin n → Term α) (v : α → Nat) :
    (fun i : Fin (n + 1) => ((Fin.cons t ts : Fin (n + 1) → Term α) i).realize v) =
      Fin.cons (t.realize v) (fun i => (ts i).realize v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem vectorOfFnCons {n : Nat} (x : Nat) (xs : Fin n → Nat) :
    List.Vector.ofFn (Fin.cons x xs) = x ::ᵥ List.Vector.ofFn xs := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem initialGraphTruth {n : Nat} {α : Type}
    (f : Formula (Fin (n + 1))) (a b : Term α) (params : Fin n → Term α) (v : α → Nat) :
    (initialGraph f a b params).Realize v ↔
      f.Realize (Fin.cons (a.realize v % (b.realize v + 1))
        (fun i => (params i).realize v)) := by
  rw [initialGraph, forallFiniteTruth]
  simp only [Formula.realize_imp, betaTruth, applyGraphTruth,
    OrdinaryArithmeticBetaProof.realize_zero, Term.realize_relabel,
    Sum.elim_comp_inl, Term.realize_var, Sum.elim_inr, Nat.zero_add, one_mul]
  constructor
  · intro h
    exact h (fun _ => a.realize v % (b.realize v + 1)) rfl
  · intro h xs hx
    rw [← hx]
    exact h

theorem stepGraphTruth {n : Nat} {α : Type}
    (g : Formula (Fin (n + 3))) (a b t : Term α) (params : Fin n → Term α) (v : α → Nat) :
    (stepGraph g a b t params).Realize v ↔
    ∀ j : Nat, j < t.realize v →
      g.Realize (Fin.cons (a.realize v % (((j + 1) + 1) * b.realize v + 1))
        (Fin.cons j (Fin.cons (a.realize v % ((j + 1) * b.realize v + 1))
          (fun i => (params i).realize v)))) := by
  rw [stepGraph, forallFiniteTruth]
  simp only [Formula.realize_imp, Formula.realize_inf, strictOrderTruth, betaTruth,
    applyGraphTruth, Term.realize_relabel, Sum.elim_comp_inl, Term.realize_var,
    Sum.elim_inr, OrdinaryArithmeticBetaProof.realize_succ, realize_cons,
    Nat.succ_eq_add_one]
  constructor
  · intro h j hj
    exact h ![j, a.realize v % ((j + 1) * b.realize v + 1),
      a.realize v % (((j + 1) + 1) * b.realize v + 1)] ⟨⟨hj, rfl⟩, rfl⟩
  · intro h xs hx
    obtain ⟨⟨hj, hp⟩, hn⟩ := hx
    rw [← hp, ← hn]
    exact h (xs 0) hj

theorem actualRecursionGraph : ActualRecursionGraph := by
  intro n f g F G hf hg v
  rw [recursionGraph, existsFiniteTruth]
  simp only [Formula.realize_inf, initialGraphTruth, stepGraphTruth, betaTruth,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, hf, hg,
    Fin.cons_zero, Fin.cons_succ]
  let params := List.Vector.ofFn (fun i : Fin n => v i.succ.succ)
  let run : Nat → Nat := fun j =>
    Nat.rec (evaluate f params) (fun k previous => evaluate g (k ::ᵥ previous ::ᵥ params)) j
  have run_zero : run 0 = evaluate f params := rfl
  have run_succ (j : Nat) : run (j + 1) = evaluate g (j ::ᵥ run j ::ᵥ params) := rfl
  have veq : List.Vector.ofFn (fun i : Fin (n + 1) => v i.succ) = v 1 ::ᵥ params := by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [params]
  have evaleq : evaluate (.recursion f g) (List.Vector.ofFn (fun i => v i.succ)) =
      run (v 1) := by
    rw [veq]
    rfl
  rw [evaleq]
  constructor
  · rintro ⟨xs, ⟨hbase, hstep⟩, hlast⟩
    let entry : Nat → Nat := fun j => xs 0 % ((j + 1) * xs 1 + 1)
    have hentry : ∀ j, j ≤ v 1 → entry j = run j := by
      intro j
      induction j with
      | zero =>
        intro _
        simpa [entry, run_zero] using hbase.symm
      | succ j ih =>
        intro hj
        have hi := ih (Nat.le_of_succ_le hj)
        have hs := hstep j (Nat.lt_of_succ_le hj)
        change evaluate g (List.Vector.ofFn (Fin.cons j (Fin.cons (entry j)
          (fun i => v i.succ.succ)))) = entry (j + 1) at hs
        rw [vectorOfFnCons, vectorOfFnCons, hi] at hs
        exact hs.symm.trans (run_succ j).symm
    exact (hentry (v 1) (Nat.le_refl _)).symm.trans hlast
  · intro h
    let l := List.ofFn (fun i : Fin (v 1 + 1) => run (i : Nat))
    obtain ⟨a, b, hab⟩ := OrdinaryArithmeticBetaProof.finiteSequenceWitness l
    have entry_eq (j : Nat) (hj : j ≤ v 1) : a % ((j + 1) * b + 1) = run j := by
      have hjl : j < l.length := by simp [l]; omega
      have hcode := hab ⟨j, hjl⟩
      rw [betaGraph, betaTruth] at hcode
      change a % ((j + 1) * b + 1) = l[j]'hjl at hcode
      simpa only [l, List.getElem_ofFn] using hcode
    refine ⟨![a, b], ⟨?_, ?_⟩, ?_⟩
    · change evaluate f params = a % (b + 1)
      have hzero := entry_eq 0 (Nat.zero_le _)
      simpa only [Nat.zero_add, one_mul, run_zero] using hzero.symm
    · intro j hj
      change evaluate g (List.Vector.ofFn (Fin.cons j
        (Fin.cons (a % ((j + 1) * b + 1)) (fun i => v i.succ.succ)))) =
        a % ((j + 1 + 1) * b + 1)
      rw [entry_eq j (Nat.le_of_lt hj), entry_eq (j + 1) (by omega)]
      rw [vectorOfFnCons, vectorOfFnCons]
    · exact (entry_eq (v 1) (Nat.le_refl _)).trans h

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionProof
