module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrder
open BalancedSyntax BalancedEvaluation

/-- Each atom retains its own WHOLE balanced pair certificate, including the
shared original basis and any outside remainder. Source binders are positive,
as required by the original balanced semantics; Nat-zero binders are not added. -/
inductive Formula where
  | compare (shape : List Nat) (certificate : Certificate shape)
      (left right : Syntax shape) (desired : Int)
  | negative (body : Formula)
  | conjunction (left right : Formula)
  | existsPositive (name : Nat) (body : Formula)

def Formula.certified : Formula → Prop
  | .compare Γ C E F _ => genuineCertificate Γ C ∧ genuineExpression Γ E ∧ genuineExpression Γ F
  | .negative p => p.certified
  | .conjunction p q => p.certified ∧ q.certified
  | .existsPositive _ p => p.certified

noncomputable def Formula.eval (ν : Nat → Nat) : Formula → Prop
  | .compare Γ C E F d => Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = d
  | .negative p => ¬p.eval ν
  | .conjunction p q => p.eval ν ∧ q.eval ν
  | .existsPositive i p => ∃ n : Nat, 0 < n ∧ p.eval (Function.update ν i n)

def Formula.variables : Formula → List Nat
  | .compare Γ C E F _ => rawVariables Γ C E ++ rawVariables Γ C F
  | .negative p => p.variables
  | .conjunction p q => p.variables ++ q.variables
  | .existsPositive i p => p.variables.filter (fun j => j != i)

/-- Positivity is required on precisely the original FREE names. Outside
coordinates, including a shadowed binder's old value, are unrestricted. -/
def positive (ν : Nat → Nat) (p : Formula) : Prop := ∀ i ∈ p.variables, 0 < ν i

def Formula.encode : Formula → Nat
  | .compare Γ C E F d => 4 * Encodable.encode (Γ, encodeCertificate Γ C, encodeSyntax Γ E, encodeSyntax Γ F, d)
  | .negative p => 4 * p.encode + 1
  | .conjunction p q => 4 * Nat.pair p.encode q.encode + 2
  | .existsPositive i p => 4 * Nat.pair i p.encode + 3

noncomputable def translate : Formula → SourceFormula
  | .compare Γ C E F d => BaseBooleanSource.translate (BalancedExactVariables.sourceFormula Γ C E F d)
  | .negative p => .negative (translate p)
  | .conjunction p q => .conjunction (translate p) (translate q)
  | .existsPositive i p => .existsNat i (.conjunction (.less (.numeral 0) (.variable i)) (translate p))

def forallPositive (i : Nat) (p : Formula) : Formula := .negative (.existsPositive i (.negative p))

namespace Code
def atom (n : Nat) : BalancedRawCompiler.Input := (Encodable.decode n).getD ([], 0, 0, 0, 0)
noncomputable def translate (code : Nat) : Nat :=
  if code % 4 = 0 then BaseBooleanSource.Code.compile (BalancedExactVariables.outputCode (atom (code / 4)))
  else if code % 4 = 1 then 5 * translate (code / 4) + 2
  else if code % 4 = 2 then 5 * Nat.pair (translate (code / 4).unpair.1) (translate (code / 4).unpair.2) + 3
  else 5 * Nat.pair (code / 4).unpair.1
    (5 * Nat.pair (CommonHeadFirstOrder.Code.positiveGuard (code / 4).unpair.1) (translate (code / 4).unpair.2) + 3) + 4
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrder
