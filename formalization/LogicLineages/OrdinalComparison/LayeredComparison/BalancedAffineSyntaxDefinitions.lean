module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine

def numeral : (Γ : List Nat) → Nat → Syntax Γ
  | [], n => .numeral n
  | _::_, n => ⟨n,fun _ => 0,[]⟩

def add : (Γ : List Nat) → Syntax Γ → Syntax Γ → Syntax Γ
  | [], E, F => .add E F
  | _::_, E, F => ⟨E.constant+F.constant,fun j => E.outside j+F.outside j,E.atoms++F.atoms⟩

/-- Literal finite repeated addition; zero multiples have empty support. -/
def scale (Γ : List Nat) (n : Nat) (E : Syntax Γ) : Syntax Γ :=
  (List.replicate n E).foldr (add Γ) (numeral Γ 0)

def combination (Γ : List Nat) (k c : Nat) (coefficients : Fin k → Nat)
    (basis : Fin k → Syntax Γ) : Syntax Γ :=
  add Γ (numeral Γ c)
    ((List.ofFn (fun j => scale Γ (coefficients j) (basis j))).foldr (add Γ) (numeral Γ 0))

/-- The actual outside part descends under the SAME lower certificate C.1. -/
def lowerPart (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ)) (E : Upper k) : Syntax Γ :=
  combination Γ k E.constant E.outside C.2

/-- Complete norm-input expression, not an independently valued new variable. -/
noncomputable def completeInput (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
    (a : Atom k) : Syntax Γ :=
  combination Γ k (actualOrdinalNorm a.head.1.repr+a.offset) (fun j => a.factors j+1) C.2
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine
