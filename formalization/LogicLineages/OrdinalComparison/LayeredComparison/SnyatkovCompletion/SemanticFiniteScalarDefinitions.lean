module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticCoefficientDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalar
open Source.ForwardTranslation CommonLayerSyntax

/-- The actual semantic finiteness condition on EVERY fixed closed coefficient
in the original scalar tree. This does not test mere Omega absence. -/
def finiteHeads {ι : Type} : Scalar ι → Prop
  | .one | .var _ => True
  | .add a b => finiteHeads a ∧ finiteHeads b
  | .shift c a => c.evaluate.1.repr < Ordinal.omega0 ∧ finiteHeads a

/-- Actual literal BASE translation using complete semantic coefficient
recognition and the already checked finite Phi expansion. -/
def compile {ι : Type} (index : ι → Nat) : Scalar ι → Option BaseTerm
  | .one => some (.numeral 1)
  | .var i => some (.variable (index i))
  | .add a b => do return .add (← compile index a) (← compile index b)
  | .shift c a => do return FiniteCoefficientBase.expand (← SemanticCoefficient.Code.recognize (closedPositiveCode c)) (← compile index a)

namespace Code
def compile (code : Nat) : Option Nat :=
  if code % 4 = 0 then some code
  else if code % 4 = 1 then some code
  else if code % 4 = 2 then do return 4 * Nat.pair (← compile (code / 4).unpair.1) (← compile (code / 4).unpair.2) + 2
  else do return FiniteCoefficientBase.Code.expand (← SemanticCoefficient.Code.recognize (code / 4).unpair.1) (← compile (code / 4).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega
end Code
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalar
