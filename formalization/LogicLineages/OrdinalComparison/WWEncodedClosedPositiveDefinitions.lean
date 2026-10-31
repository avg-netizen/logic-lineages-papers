module
public import LogicLineages.OrdinalComparison.WWEncodedBaseTwoDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedScalarDefinitions
public import LogicLineages.OrdinalComparison.EncodedNaturalProductDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

def closedPositiveCode : ClosedPositive → Nat
  | .one => 0
  | .omega => 1
  | .add a b => 4 * Nat.pair (closedPositiveCode a) (closedPositiveCode b) + 2
  | .emul a b => 4 * Nat.pair (closedPositiveCode a) (closedPositiveCode b) + 3

/-- Actual normal-note code evaluation of closed positive syntax. Malformed
leaf tags are totalized explicitly; correctness refers to the exact source
encoder. No precomputed normal head or ordinal-evaluation oracle is supplied. -/
def encodedClosedPositive : Nat → Nat
  | n =>
    if h0 : n % 4 = 0 then rawNoteEncode (ClosedPositive.one.evaluate).1
    else if h1 : n % 4 = 1 then rawNoteEncode (ClosedPositive.omega.evaluate).1
    else
      have hn : 0 < n := by omega
      have hd : n / 4 < n := Nat.div_lt_self hn (by decide)
      let p := (n / 4).unpair
      have hl : p.1 < n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2 < n := (Nat.unpair_right_le _).trans_lt hd
      if n % 4 = 2 then encodedNaturalSum (encodedClosedPositive p.1) (encodedClosedPositive p.2)
      else encodedNaturalProduct (encodedBaseTwoPower (encodedClosedPositive p.1)) (encodedClosedPositive p.2)
termination_by n => n
decreasing_by all_goals assumption

def encodedClosedHead (n : Nat) : Nat :=
  encodedNaturalProduct (rawNoteEncode ClosedPositive.omega.evaluate.1) (encodedClosedPositive n)
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
