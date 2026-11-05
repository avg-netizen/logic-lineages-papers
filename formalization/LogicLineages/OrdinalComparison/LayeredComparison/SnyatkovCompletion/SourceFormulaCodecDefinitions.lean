module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodec
open CommonLayerSyntax

/-- Every radix-five code denotes literal source syntax. The already defined
radix-four term decoder is used unchanged for atom operands. -/
def decode (code : Nat) : SourceFormula :=
  if code % 5 = 0 then .equal (BaseTerm.decode (code / 5).unpair.1) (BaseTerm.decode (code / 5).unpair.2)
  else if code % 5 = 1 then .less (BaseTerm.decode (code / 5).unpair.1) (BaseTerm.decode (code / 5).unpair.2)
  else if code % 5 = 2 then .negative (decode (code / 5))
  else if code % 5 = 3 then .conjunction (decode (code / 5).unpair.1) (decode (code / 5).unpair.2)
  else .existsNat (code / 5).unpair.1 (decode (code / 5).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodec
