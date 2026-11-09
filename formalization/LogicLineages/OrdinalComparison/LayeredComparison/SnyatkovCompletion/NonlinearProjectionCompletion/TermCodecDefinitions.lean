module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ContractDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodec

/-- A total decoder for the ORIGINAL expanded-term radix10. Every natural
code denotes a literal term, not a semantic or independently chosen value. -/
def decode (code : Nat) : Term :=
  if code % 10 = 0 then .numeral (code / 10)
  else if code % 10 = 1 then .variable (code / 10)
  else if code % 10 = 2 then
    .add (decode (code / 10).unpair.1) (decode (code / 10).unpair.2)
  else if code % 10 = 3 then
    .subtract (decode (code / 10).unpair.1) (decode (code / 10).unpair.2)
  else if code % 10 = 4 then .multiply (code / 10).unpair.1 (decode (code / 10).unpair.2)
  else if code % 10 = 5 then .divide (code / 10).unpair.1 (decode (code / 10).unpair.2)
  else if code % 10 = 6 then .phi (decode (code / 10))
  else if code % 10 = 7 then .hyper (decode (code / 10))
  else if code % 10 = 8 then .phiInverse (decode (code / 10))
  else .hyperInverse (decode (code / 10))
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 10 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 10)
    have hr := Nat.unpair_right_le (code / 10)
    omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodec
