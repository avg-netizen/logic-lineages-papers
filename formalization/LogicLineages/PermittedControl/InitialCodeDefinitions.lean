module
public import LogicLineages.PermittedControl.PureCertificateDefinitions
public import LogicLineages.PermittedControl.InitialPeelingDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Total original-unit list table on the actual raw ONote encoding.
Coefficients are expanded with multiplicity, in original descending order. -/
def originalUnitCodeTable : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => originalUnitCodeTable n ++
      [List.replicate (n.unpair.2.unpair.1+1) n.unpair.1 ++
        (originalUnitCodeTable n).getD n.unpair.2.unpair.2 []]

def originalUnitCodes (delta : Nat) : List Nat := (originalUnitCodeTable delta).getD delta []

/-- Literal original leading unit, with total zero fallback only for empty
raw lists. Correctness below is restricted to positive limit gaps. -/
def originalLeadingCode (delta : Nat) : Nat := (originalUnitCodes delta).headD 0

def originalQuadraticRemainder (l : List Nat) : Bool :=
  decide (l.head?=some (rawNoteEncode (ONote.ofNat 2))) &&
    l.tail.all (fun e => decide (e=rawNoteEncode (ONote.ofNat 1)))

/-- Executable source initial-pass predicate. Generated units never enter
this program. The two quadratic exception shapes remain explicit. -/
def initialPassCode (mu nu delta : Nat) : Bool :=
  let l := originalUnitCodes delta
  let E := originalLeadingCode delta
  let c := rawProfileCode mu E
  let d := rawProfileCode nu E
  decide (c=d) || l.tail.all (fun e => decide (rawComparisonCode e (rawNoteEncode (ONote.ofNat 2))=0)) ||
    (decide (c=d+1 ∨ d=c+1) &&
      ((decide (rawComparisonCode (rawNoteEncode (ONote.ofNat 3)) E ≠ 2) && originalQuadraticRemainder l.tail) ||
       (decide (E=rawNoteEncode (ONote.ofNat 2)) && originalQuadraticRemainder l.tail)) &&
      decide ((min c d+(1+rawNormCode E))%2=1))

end LogicLineages.PermittedControl
