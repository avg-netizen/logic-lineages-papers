module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrder
open CommonLayerSyntax

/-- Each atom retains its OWN actual finite head certificate and literal typed
operands. No shared head list, independent child valuation, or flattened binder
prefix is assumed. The two binder domains are distinguished explicitly. -/
inductive Formula where
  | compare (heads : List NONote) (left right : CommonSyntax heads.length) (desired : Int)
  | negative (body : Formula)
  | conjunction (left right : Formula)
  | existsNat (name : Nat) (body : Formula)
  | existsPositive (name : Nat) (body : Formula)

def Formula.certified : Formula → Prop
  | .compare heads _ _ _ => genuineHeads heads
  | .negative p => p.certified
  | .conjunction p q => p.certified ∧ q.certified
  | .existsNat _ p | .existsPositive _ p => p.certified

noncomputable def Formula.eval (ν : Nat → Nat) : Formula → Prop
  | .compare heads E F d => Int.sign ((commonValue heads E ν : Int) - (commonValue heads F ν : Int)) = d
  | .negative p => ¬p.eval ν
  | .conjunction p q => p.eval ν ∧ q.eval ν
  | .existsNat i p => ∃ n : Nat, p.eval (Function.update ν i n)
  | .existsPositive i p => ∃ n : Nat, 0 < n ∧ p.eval (Function.update ν i n)

def Formula.variables : Formula → List Nat
  | .compare heads E F _ => commonVariables heads.length E ++ commonVariables heads.length F
  | .negative p => p.variables
  | .conjunction p q => p.variables ++ q.variables
  | .existsNat i p | .existsPositive i p => p.variables.filter (fun j => j != i)

def Formula.encode : Formula → Nat
  | .compare heads E F d => 5 * Encodable.encode (headCodes heads, encodeCommon heads.length E, encodeCommon heads.length F, d)
  | .negative p => 5 * p.encode + 1
  | .conjunction p q => 5 * Nat.pair p.encode q.encode + 2
  | .existsNat i p => 5 * Nat.pair i p.encode + 3
  | .existsPositive i p => 5 * Nat.pair i p.encode + 4

noncomputable def translate : Formula → SourceFormula
  | .compare heads E F d => BaseBooleanSource.translate
      (CommonHeadExactVariables.formula (headCodes heads) (encodeCommon heads.length E) (encodeCommon heads.length F) d)
  | .negative p => .negative (translate p)
  | .conjunction p q => .conjunction (translate p) (translate q)
  | .existsNat i p => .existsNat i (translate p)
  | .existsPositive i p => .existsNat i (.conjunction (.less (.numeral 0) (.variable i)) (translate p))

def forallNat (i : Nat) (p : Formula) : Formula := .negative (.existsNat i (.negative p))
def forallPositive (i : Nat) (p : Formula) : Formula := .negative (.existsPositive i (.negative p))

namespace Code
/-- Malformed atomic payloads keep the explicit empty-head/zero comparison default.
No certification decision is used by the total numeric translation. -/
def atom (n : Nat) : CommonHeadExactVariables.Input := (Encodable.decode n).getD ([], 0, 0, 0)
def positiveGuard (i : Nat) : Nat := 5 * Nat.pair 0 (4 * i + 1) + 1
noncomputable def translate (code : Nat) : Nat :=
  if code % 5 = 0 then BaseBooleanSource.Code.compile (CommonHeadExactVariables.output (atom (code / 5)))
  else if code % 5 = 1 then 5 * translate (code / 5) + 2
  else if code % 5 = 2 then 5 * Nat.pair (translate (code / 5).unpair.1) (translate (code / 5).unpair.2) + 3
  else if code % 5 = 3 then 5 * Nat.pair (code / 5).unpair.1 (translate (code / 5).unpair.2) + 4
  else 5 * Nat.pair (code / 5).unpair.1
    (5 * Nat.pair (positiveGuard (code / 5).unpair.1) (translate (code / 5).unpair.2) + 3) + 4
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrder
