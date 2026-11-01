module
public import LogicLineages.OrdinalComparison.SingleCoreEvaluationDefinitions
public import LogicLineages.OrdinalComparison.ComparisonAssemblyDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

structure SingleCoreRowAtom where
  head : NONote
  coefficient : Int
  multiplier : Nat
  offset : Nat

structure SingleCoreRow where
  constant : Int
  linear : Int
  atoms : List SingleCoreRowAtom

def singleCoreRowValid (row : SingleCoreRow) : Prop :=
  ∀ atom∈row.atoms,Order.IsSuccLimit atom.head.1.repr ∧ 0<atom.multiplier

noncomputable def actualSingleCoreRowValue (row : SingleCoreRow) (t : Nat) : Int :=
  row.constant+row.linear*(t : Int)+
    (row.atoms.map (fun atom => atom.coefficient*
      (actualProfileHead atom.head (atom.multiplier*t+atom.offset) : Int))).sum

def positiveSourceMultiple : Nat → FixedLimitPositiveExpr → FixedLimitPositiveExpr
  | 0, _ => .constant 0
  | n+1, E => .add (positiveSourceMultiple n E) E

def encodedPositiveSourceMultiple : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, source => 4*Nat.pair (encodedPositiveSourceMultiple n source) source+2

def singleCoreAtomPositive (atom : SingleCoreRowAtom) : FixedLimitPositiveExpr :=
  .head atom.head (.add (positiveInputMultiple atom.multiplier) (.constant atom.offset))

def singleCoreCoefficientPart (negative : Bool) (coefficient : Int) : Nat :=
  if negative then (-coefficient).toNat else coefficient.toNat

def singleCoreRowPart (negative : Bool) (row : SingleCoreRow) : FixedLimitPositiveExpr :=
  .add (.constant (singleCoreCoefficientPart negative row.constant))
    (.add (positiveInputMultiple (singleCoreCoefficientPart negative row.linear))
      (row.atoms.foldr (fun atom rest =>
        .add (positiveSourceMultiple (singleCoreCoefficientPart negative atom.coefficient)
          (singleCoreAtomPositive atom)) rest) (.constant 0)))

abbrev SingleCoreAtomCode := Nat × (Nat × Nat) × Nat × Nat
abbrev EncodedSingleCoreRow := (Nat × Nat) × (Nat × Nat) × List SingleCoreAtomCode

/-- Faithful finite signed-integer data use two natural parts. The numeric
compiler's totality does not need a separate Primcodable Int interface. -/
def singleCoreCoefficientCode (coefficient : Int) : Nat × Nat := (coefficient.toNat,(-coefficient).toNat)

def singleCoreAtomCode (atom : SingleCoreRowAtom) : SingleCoreAtomCode :=
  (rawNoteEncode atom.head.1,singleCoreCoefficientCode atom.coefficient,atom.multiplier,atom.offset)

def singleCoreRowCode (row : SingleCoreRow) : EncodedSingleCoreRow :=
  (singleCoreCoefficientCode row.constant,singleCoreCoefficientCode row.linear,row.atoms.map singleCoreAtomCode)

def encodedSingleCoreAtomPositive (atom : SingleCoreAtomCode) : Nat :=
  4*Nat.pair atom.1 (4*Nat.pair (positiveInputMultipleCode atom.2.2.1) (4*atom.2.2.2)+2)+3

def encodedSingleCoreRowPart (negative : Bool) (row : EncodedSingleCoreRow) : Nat :=
  let constant := if negative then row.1.2 else row.1.1
  let linear := if negative then row.2.1.2 else row.2.1.1
  let atoms := row.2.2.foldr (fun atom rest =>
    4*Nat.pair (encodedPositiveSourceMultiple (if negative then atom.2.1.2 else atom.2.1.1)
      (encodedSingleCoreAtomPositive atom)) rest+2) 0
  4*Nat.pair (4*constant) (4*Nat.pair (positiveInputMultipleCode linear) atoms+2)+2

def encodedSingleCoreRowParts (row : EncodedSingleCoreRow) : Nat × Nat :=
  (encodedSingleCoreRowPart false row,encodedSingleCoreRowPart true row)

noncomputable def encodedSingleCoreRowSign (row : EncodedSingleCoreRow) : Nat × Nat :=
  let parts := encodedSingleCoreRowParts row
  encodedOneVariableSignDecision (2*parts.1) (2*parts.2)

end LogicLineages.OrdinalComparison
