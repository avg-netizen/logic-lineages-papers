module

public import Init

@[expose] public section


/-!
# Literal positive exponential expressions

This is the independently written syntax and numerical semantics for paper 02.
The constructors are exactly one, positive-valued variables, addition and
`E(a,b) = 2^a * b`. No general multiplication or zero term is introduced.
The computability, normal-form and source-assignment correspondence targets
are separate obligations; these definitions do not discharge them.
-/

namespace LogicLineages.ComputabilityKnowledge.PositiveExpression

/-- Positive naturals, spelled out so this syntax requires only Lean's core. -/
abbrev PosNat := {n : Nat // 0 < n}

inductive Expr (ι : Type) where
  | one : Expr ι
  | var : ι → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | emul : Expr ι → Expr ι → Expr ι

def Expr.eval {ι : Type} (ρ : ι → PosNat) : Expr ι → Nat
  | .one => 1
  | .var i => (ρ i : Nat)
  | .add a b => a.eval ρ + b.eval ρ
  | .emul a b => 2 ^ a.eval ρ * b.eval ρ

def Expr.depth {ι : Type} : Expr ι → Nat
  | .one => 0
  | .var _ => 0
  | .add a b => max a.depth b.depth
  | .emul a b => max a.depth b.depth + 1

def Expr.rename {ι κ : Type} (f : ι → κ) : Expr ι → Expr κ
  | .one => .one
  | .var i => .var (f i)
  | .add a b => .add (a.rename f) (b.rename f)
  | .emul a b => .emul (a.rename f) (b.rename f)

@[simp] theorem eval_one {ι : Type} (ρ : ι → PosNat) :
    (Expr.one : Expr ι).eval ρ = 1 := rfl

@[simp] theorem eval_var {ι : Type} (ρ : ι → PosNat) (i : ι) :
    (Expr.var i).eval ρ = (ρ i : Nat) := rfl

@[simp] theorem eval_add {ι : Type} (ρ : ι → PosNat) (a b : Expr ι) :
    (Expr.add a b).eval ρ = a.eval ρ + b.eval ρ := rfl

@[simp] theorem eval_emul {ι : Type} (ρ : ι → PosNat) (a b : Expr ι) :
    (Expr.emul a b).eval ρ = 2 ^ a.eval ρ * b.eval ρ := rfl

private theorem congrNat2 (f : Nat → Nat → Nat) {a b c d : Nat}
    (h : a = b) (k : c = d) : f a c = f b d := by
  cases h
  cases k
  rfl

@[simp] theorem eval_rename {ι κ : Type} (f : ι → κ) (ρ : κ → PosNat)
    (a : Expr ι) : (a.rename f).eval ρ = a.eval (ρ ∘ f) := by
  induction a with
  | one => rfl
  | var i => rfl
  | add a b ha hb => exact congrNat2 Nat.add ha hb
  | emul a b ha hb =>
      exact congrNat2 Nat.mul (congrArg (fun n : Nat => 2 ^ n) ha) hb

@[simp] theorem depth_rename {ι κ : Type} (f : ι → κ) (a : Expr ι) :
    (a.rename f).depth = a.depth := by
  induction a with
  | one => rfl
  | var i => rfl
  | add a b ha hb => exact congrNat2 Nat.max ha hb
  | emul a b ha hb => exact congrArg (fun n : Nat => n + 1) (congrNat2 Nat.max ha hb)

def ExtensionalEq {ι : Type} (a b : Expr ι) : Prop :=
  ∀ ρ : ι → PosNat, a.eval ρ = b.eval ρ

def UniversalLE {ι : Type} (a b : Expr ι) : Prop :=
  ∀ ρ : ι → PosNat, a.eval ρ ≤ b.eval ρ

def UniversalLT {ι : Type} (a b : Expr ι) : Prop :=
  ∀ ρ : ι → PosNat, a.eval ρ < b.eval ρ

end LogicLineages.ComputabilityKnowledge.PositiveExpression
