module
public import LogicLineages.PermittedControl.SelectedGeneratedSourceTargets
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.GroundComparisonPositive
open OrdinalComparison Source Source.ForwardTranslation

/-- Raw code of the zero notation, used for zero padding. -/
def zeroNoteCode : Nat := rawNoteEncode (0 : ONote)

/-- One raw coordinate test on normal-note codes: `equal` asks `=`, otherwise `≤`. -/
def coordTest (equal : Bool) (a b : Nat) : Bool :=
  if equal = true then decide (rawComparisonCode a b = 1) else decide (rawComparisonCode a b ≠ 2)

/-- Raw positive-coordinate test on two lists of closed positive syntax
codes (`closedPositiveCode`), evaluated by `encodedClosedPositive`, with zero
padding of the shorter list. -/
def positiveTest (equal : Bool) (as bs : List Nat) : Bool :=
  (List.range (max as.length bs.length)).foldr
    (fun j acc => coordTest equal ((as.map encodedClosedPositive).getD j zeroNoteCode)
      ((bs.map encodedClosedPositive).getD j zeroNoteCode) && acc) true

/-- The ordinal value of position `j` of a list of closed positive fields, zero beyond it. -/
noncomputable def paddedValue (zs : List ClosedPositive) (j : Nat) : Ordinal.{0} :=
  (zs.map (fun z => z.evaluate.1.repr)).getD j 0

def ExactPositiveTest : Prop :=
  ∀ (equal : Bool) (as bs : List ClosedPositive),
    positiveTest equal (as.map closedPositiveCode) (bs.map closedPositiveCode) = true ↔
      ∀ j : Nat, if equal = true then paddedValue as j = paddedValue bs j
        else paddedValue as j ≤ paddedValue bs j

def PositiveTestEffectivity : Prop :=
  Primrec (fun x : Bool × List Nat × List Nat => positiveTest x.1 x.2.1 x.2.2)

def FullGroundComparisonPositive : Prop := ExactPositiveTest ∧ PositiveTestEffectivity

end LogicLineages.PermittedControl.GroundComparisonPositive
