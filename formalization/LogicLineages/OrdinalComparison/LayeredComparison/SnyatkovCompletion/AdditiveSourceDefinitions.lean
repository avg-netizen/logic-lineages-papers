module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSource
open CommonLayerSyntax

/-- The literal additive source grammar: constants, original names and sums.
A Phi node is rejected even if it has a constant or semantically unused input. -/
def termTest : BaseTerm → Bool
  | .numeral _ | .variable _ => true
  | .add a b => termTest a && termTest b
  | .phi _ => false

def test : SourceFormula → Bool
  | .equal a b | .less a b => termTest a && termTest b
  | .negative p => test p
  | .conjunction p q => test p && test q
  | .existsNat _ p => test p

/-- The actual prior source translation followed by linear-name elimination. -/
def eliminate (p : SourceFormula) : NormalForm.Formula :=
  QuantifiedLinear.eliminate (SourceRows.translate p)

def decideClosed (p : SourceFormula) : Option Bool :=
  if test p then ClosedLinear.decideClosed (SourceRows.translate p) else none

namespace Code
def termTest (code : Nat) : Bool :=
  (SourceTermGraph.Code.instructions code).all (fun op => op.1 != 3)

def test (code : Nat) : Bool :=
  if code % 5 = 0 ∨ code % 5 = 1 then
    termTest (code / 5).unpair.1 && termTest (code / 5).unpair.2
  else if code % 5 = 2 then test (code / 5)
  else if code % 5 = 3 then test (code / 5).unpair.1 && test (code / 5).unpair.2
  else test (code / 5).unpair.2
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def eliminate (code : Nat) : Nat :=
  QuantifiedLinear.Code.eliminate (SourceRows.Code.translate code)

def decideClosed (code : Nat) : Option Bool :=
  if test code then ClosedLinear.Code.decideClosed (SourceRows.Code.translate code) else none
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSource
