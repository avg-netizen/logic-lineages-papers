module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.PerturbedControl.Targets

/-- Exact two-adic valuation supplier, including its primitive recursion and
maximality; no unproved v2 computability premise. -/
def Valuation : Prop :=
  Primrec₂ search ∧ Primrec valuationTwo ∧ valuationTwo 0=0 ∧
  ∀ n : Nat, 0<n → 2^(valuationTwo n) ∣ n ∧ ¬ 2^(valuationTwo n+1) ∣ n

/-- Whole paper09 lem:perturbed-control. The source itself fixes a primitive
recursive bounded-simulation H; universal Boolean H is a genuine strengthening
because these control properties use only its zero/one output. This theorem
makes NO halting completeness or perturbed-control hardness claim. -/
def FullPerturbedControl : Prop := Valuation ∧
  ∀ (H : Nat×Nat → Bool), Primrec H → ∀ b : Nat,
    Primrec (control b H) ∧
    (∀ n : Nat, n≤b → control b H n=Phi n) ∧
    (∀ n : Nat, 0≤control b H n-Phi n ∧ control b H n-Phi n≤1) ∧
    (∀ n : Nat, Phi n≤control b H n ∧ control b H n<Phi (n+1)) ∧
    (∀ n : Nat, 4*control b H n<control b H (n+1)) ∧
    (∀ v a : Nat, 1≤a → control b H v+2*a≤control b H (v+a)) ∧
    (∀ n : Nat, 101≤n → control b H n≤fastControl 6 n) ∧
    RatioLimit b H
end LogicLineages.OrdinalComparison.PerturbedControl.Targets
