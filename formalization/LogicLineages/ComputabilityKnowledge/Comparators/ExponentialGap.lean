module

public import LogicLineages.ComputabilityKnowledge.PositiveExpression

@[expose] public section


/-!
# Independent paper-02 collision-detector comparator

Codex owns this specification. An author proves it in a different module.
`systemLeft` and `systemRight` are the literal source terms U and V in the
depth-two reduction, including the initial one and the empty-system case.
The target is a complete local reduction lemma, not the paper's complete
undecidability or decision classification. No missing MRDP supplier appears
as an assumption in this statement.
-/

namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialGap

open PositiveExpression

def leftPair {ι : Type} (a b : Expr ι) : Expr ι :=
  .add (.emul (.add a a) .one) (.emul (.add b b) .one)

def rightPair {ι : Type} (a b : Expr ι) : Expr ι :=
  .emul (.add (.add a b) .one) .one

def systemLeft {ι : Type} : List (Expr ι × Expr ι) → Expr ι
  | [] => .one
  | (a, b) :: rest => .add (leftPair a b) (systemLeft rest)

def systemRight {ι : Type} : List (Expr ι × Expr ι) → Expr ι
  | [] => .one
  | (a, b) :: rest => .add (rightPair a b) (systemRight rest)

def AllEquations {ι : Type} (ρ : ι → PosNat)
    (equations : List (Expr ι × Expr ι)) : Prop :=
  ∀ pair ∈ equations, pair.1.eval ρ = pair.2.eval ρ

/-- The independently fixed local target. No proof data are arguments. -/
def Target : Prop :=
  ∀ (d : Nat) (equations : List (Expr (Fin d) × Expr (Fin d)))
      (ρ : Fin d → PosNat),
    (systemRight equations).eval ρ ≤ (systemLeft equations).eval ρ ∧
      ((systemLeft equations).eval ρ = (systemRight equations).eval ρ ↔
        AllEquations ρ equations)

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialGap
