module

public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShift
public import Mathlib.NumberTheory.Dioph

@[expose] public section

/-! Existential interfaces for the pinned Mathlib Diophantine supplier.
Mathlib's `Dioph` permits an arbitrary auxiliary type: finite witnesses below
must therefore be proved sufficient, not assumed. These interfaces assert no
computable extraction from extensional `Poly`, `IsPoly`, or `Dioph` proofs.
The concrete power graph is a supplier component, not full DPRM/MRDP. -/
namespace LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridge

open PolynomialCircuit

def sumIndex (n m : Nat) : Fin n ⊕ Fin m → Nat :=
  Sum.elim (fun i => i.val) (fun j => n+j.val)

def joinedNat {n m : Nat} (ν : Fin n → Nat) (w : Fin m → Nat) : Nat → Nat :=
  fun i => if h : i < n then ν ⟨i,h⟩ else
    if h' : i-n < m then w ⟨i-n,h'⟩ else 0

def FiniteDiophantine {n : Nat} (S : Set (Fin n → Nat)) : Prop :=
  ∃ (m : Nat) (P : MvPolynomial (Fin n ⊕ Fin m) Int),
    ∀ ν, ν ∈ S ↔ ∃ w : Fin m → Nat,
      MvPolynomial.eval (fun i => ((Sum.elim ν w i : Nat) : Int)) P = 0

def CodeRepresents {n : Nat} (S : Set (Fin n → Nat)) (m : Nat) (p : Code) : Prop :=
  p.inputCount = n+m ∧ p.WellFormed ∧
    ∀ ν, ν ∈ S ↔ ∃ w : Fin m → Nat,
      MvPolynomial.eval (fun i => (joinedNat ν w i : Int)) (interpret p) = 0

def powerGraph : Set (Fin 3 → Nat) := {ν | ν 0 ^ ν 1 = ν 2}

end LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridge
