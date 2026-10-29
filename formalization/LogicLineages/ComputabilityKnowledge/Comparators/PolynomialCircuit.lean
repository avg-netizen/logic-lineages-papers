module

public import LogicLineages.ComputabilityKnowledge.PolynomialCircuit

@[expose] public section

/-! Independent full positive-polynomial circuit front-end comparator.
The natural positive/negative totals are interpreted in Int explicitly.
Coverage includes all MvPolynomial(Fin n) Int, not merely our own syntax.
No MRDP, zero-input-domain conversion or admissible-source-vector claim. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PolynomialCircuit

open PositiveExpression CircuitReduction
open LogicLineages.ComputabilityKnowledge.PolynomialCircuit

def InterpretationCorrect : Prop :=
  ∀ (p : Code) (ρ : Nat → PosNat),
    MvPolynomial.eval (fun i => ((ρ i).val : Int)) (interpret p) =
      (positiveTotal ρ p.monomials : Int) - (negativeTotal ρ p.monomials : Int)

def CompiledWellFormed : Prop :=
  ∀ p : Code, p.WellFormed →
    (compile p).inputCount = p.inputCount ∧ (compile p).WellFormed

def OutputValues : Prop :=
  ∀ p : Code, p.WellFormed → ∀ ρ : Nat → PosNat,
    let c := compile p
    (run c.inputCount c.gates ρ c.leftOutput).val = 1 + positiveTotal ρ p.monomials ∧
    (run c.inputCount c.gates ρ c.rightOutput).val = 1 + negativeTotal ρ p.monomials

def InputsPreserved : Prop :=
  ∀ p : Code, p.WellFormed → ∀ (ρ : Nat → PosNat) (i : Nat), i < p.inputCount →
    let c := compile p
    run c.inputCount c.gates ρ i = ρ i

def FreshOutputs : Prop :=
  ∀ p : Code, p.WellFormed →
    2 ≤ (compile p).gates.length ∧
    p.inputCount ≤ (compile p).leftOutput ∧ p.inputCount ≤ (compile p).rightOutput

def ZeroIff : Prop :=
  ∀ p : Code, p.WellFormed → ∀ ρ : Nat → PosNat,
    MvPolynomial.eval (fun i => ((ρ i).val : Int)) (interpret p) = 0 ↔
      (compile p).outputEqual ρ

/-- Coverage is mathematical existence; it is not asserted to be an algorithm
on the abstract MvPolynomial quotient. Computation is on the explicit Code. -/
def Coverage : Prop :=
  ∀ (n : Nat) (P : MvPolynomial (Fin n) Int),
    ∃ p : Code, p.inputCount = n ∧ p.WellFormed ∧
      interpret p = MvPolynomial.rename (fun i : Fin n => i.val) P

def Target : Prop := InterpretationCorrect ∧ CompiledWellFormed ∧ OutputValues ∧
  InputsPreserved ∧ FreshOutputs ∧ ZeroIff ∧ Coverage

end LogicLineages.ComputabilityKnowledge.Comparators.PolynomialCircuit
