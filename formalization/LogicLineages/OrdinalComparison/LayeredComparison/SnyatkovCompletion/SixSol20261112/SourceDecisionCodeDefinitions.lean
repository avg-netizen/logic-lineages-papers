module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecision
open NonlinearProjectionCompletion

/-- Actual inclusion of the original radix-four f-only terms, without evaluation. -/
def embedTerm (code : Nat) : Nat :=
  if code % 4 = 0 then 10 * (code / 4)
  else if code % 4 = 1 then 10 * (code / 4) + 1
  else if code % 4 = 2 then WindowCode.add
    (embedTerm (code / 4).unpair.1) (embedTerm (code / 4).unpair.2)
  else WindowCode.phi (embedTerm (code / 4))
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

def binder (i code : Nat) : Nat :=
  WholeBoundProjectionCode.project (i :: BooleanGraphCode.allocated [i] code)
    (BooleanGraphCode.compile [i] code)

/-- The original all-source structural compiler, including bound-name shadowing. -/
def eliminate (code : Nat) : Nat :=
  if code % 5 = 0 then (8 * Nat.pair (embedTerm (code / 5).unpair.1) (embedTerm (code / 5).unpair.2) + 2)
  else if code % 5 = 1 then WindowCode.less
    (embedTerm (code / 5).unpair.1) (embedTerm (code / 5).unpair.2)
  else if code % 5 = 2 then WindowCode.negative (eliminate (code / 5))
  else if code % 5 = 3 then WindowCode.conjunction
    (eliminate (code / 5).unpair.1) (eliminate (code / 5).unpair.2)
  else binder (code / 5).unpair.1 (eliminate (code / 5).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 5 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

/-- Numeric evaluation at the actual all-zero valuation. Every expanded term
constructor retains its original arithmetic function, including H and inverses. -/
def groundTerm (code : Nat) : Nat :=
  if code % 10 = 0 then code / 10
  else if code % 10 = 1 then 0
  else if code % 10 = 2 then groundTerm (code / 10).unpair.1 + groundTerm (code / 10).unpair.2
  else if code % 10 = 3 then groundTerm (code / 10).unpair.1 - groundTerm (code / 10).unpair.2
  else if code % 10 = 4 then (code / 10).unpair.1 * groundTerm (code / 10).unpair.2
  else if code % 10 = 5 then groundTerm (code / 10).unpair.2 / (code / 10).unpair.1
  else if code % 10 = 6 then Phi (groundTerm (code / 10))
  else if code % 10 = 7 then FixedSeedControlResidue.H (groundTerm (code / 10))
  else if code % 10 = 8 then SnyatkovInverse.phiInverse (groundTerm (code / 10))
  else SnyatkovInverse.hyperInverse (groundTerm (code / 10))
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 10 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 10)
    have hr := Nat.unpair_right_le (code / 10)
    omega

def groundMatrix (code : Nat) : Bool :=
  if code % 8 = 0 then true else if code % 8 = 1 then false
  else if code % 8 = 2 then groundTerm (code / 8).unpair.1 == groundTerm (code / 8).unpair.2
  else if code % 8 = 3 then decide (groundTerm (code / 8).unpair.1 < groundTerm (code / 8).unpair.2)
  else if code % 8 = 4 then decide ((code / 8).unpair.1 ∣ groundTerm (code / 8).unpair.2)
  else if code % 8 = 5 then !(groundMatrix (code / 8))
  else if code % 8 = 6 then groundMatrix (code / 8).unpair.1 && groundMatrix (code / 8).unpair.2
  else groundMatrix (code / 8).unpair.1 || groundMatrix (code / 8).unpair.2
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 8 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 8)
    have hr := Nat.unpair_right_le (code / 8)
    omega

def answer (code : Nat) : Bool := groundMatrix (eliminate code)
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecision
