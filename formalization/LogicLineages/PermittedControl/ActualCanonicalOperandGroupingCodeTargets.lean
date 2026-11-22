module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTargets
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCode
open PreparedProjection ActualCanonicalOperandGrouping

/-- Receive the explicit checked-source bit and the existing serialized
list of original signed operand record bytes. A failed decode is not an
empty list or a successful all-read result. -/
def groupCode (p : Bool × Nat) : Option Nat :=
  match (Encodable.decode p.2 : Option (List RawTerm)) with
  | none => none
  | some ts => (groupCheckedRaw p.1 ts).map Encodable.encode

def ExactGroupingCodePrimitive : Prop :=
  Primrec groupRaw ∧ Primrec₂ groupCheckedRaw ∧ Primrec groupCode

def ExactGroupingCodeCalibration : Prop :=
  (∀ (gate : Bool) (ts : List RawTerm),
    groupCode (gate,Encodable.encode ts) = (groupCheckedRaw gate ts).map Encodable.encode) ∧
  (∀ b : Nat, (Encodable.decode b : Option (List RawTerm)) = none →
    ∀ gate : Bool, groupCode (gate,b) = none) ∧
  ∀ (gate : Bool) (terms : List MixedSameRankResidue.WeightedOperand),
    groupCode (gate,Encodable.encode (terms.map encodeTerm)) =
      if gate then some (Encodable.encode ((groupTyped terms).map encodeTerm)) else none

def FullActualCanonicalOperandGroupingCode : Prop :=
  ExactGroupingCodePrimitive ∧ ExactGroupingCodeCalibration

end LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCode
