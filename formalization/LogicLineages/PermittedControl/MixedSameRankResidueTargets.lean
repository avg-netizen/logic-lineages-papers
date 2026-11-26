module
public import LogicLineages.PermittedControl.OrdinaryResidueOperandTargets

@[expose] public section
namespace LogicLineages.PermittedControl.MixedSameRankResidue
open OrdinalComparison FieldComparison PreparedProjection

abbrev WeightedOperand := Int × LowerOperand
abbrev WeightedCode := Int × LowerOperandCode

def encodeWeighted (term : WeightedOperand) : WeightedCode := (term.1,term.2.code)

def properOperand : LowerOperand → Prop
  | .coordinate _ => True
  | .ordinary _ F => ProperField F
  | .count _ lam mu => ProperField (.entry 0 lam mu)

noncomputable def operandResidue (j : Nat) : LowerOperand → Int
  | .coordinate _ => (j : Int)
  | .ordinary _ F => OrdinaryResidueOperand.residue F j
  | .count _ lam mu => CountCongruenceNamedRow.residueCount
      (shortGapLength lam mu) (actualOrdinalNorm mu.1.repr) j

noncomputable def operandTail (B m : Nat) : LowerOperand → Nat
  | .coordinate _ => 0
  | .ordinary _ F => OrdinaryResidueOperand.residueTail B m F
  | .count _ lam mu =>
    max (actualOrdinalNorm lam.1.repr) (max (actualOrdinalNorm mu.1.repr + 3) (max m B))

/-- The raw numeric map is total; interpretation is confined to original
canonical operand codes. Coordinate, value and count tags stay distinct. -/
def operandResidueCode (op : LowerOperandCode) (j : Nat) : Int :=
  if op.1 = 0 then (j : Int)
  else if op.1 = 1 then OrdinaryResidueOperand.residueCode op.2.2 j
  else CountCongruenceNamedRow.residueCount
    (shortGapLengthCode op.2.2.2.2.1 op.2.2.2.2.2) (rawNormCode op.2.2.2.2.2) j

def operandTailCode (B m : Nat) (op : LowerOperandCode) : Nat :=
  if op.1 = 0 then 0
  else if op.1 = 1 then OrdinaryResidueOperand.residueTailCode B m op.2.2
  else CountCongruenceNamedRow.tailCode B op.2.2.2.2.1 op.2.2.2.2.2 m

noncomputable def weightedResidue (terms : List WeightedOperand) (j : Nat) : Int :=
  terms.foldr (fun t acc => t.1 * operandResidue j t.2 + acc) 0

noncomputable def weightedTail (B m : Nat) (terms : List WeightedOperand) : Nat :=
  terms.foldr (fun t acc => max (operandTail B m t.2) acc) 0

def weightedResidueCode (terms : List WeightedCode) (j : Nat) : Int :=
  terms.foldr (fun t acc => t.1 * operandResidueCode t.2 j + acc) 0

def weightedTailCode (B m : Nat) (terms : List WeightedCode) : Nat :=
  terms.foldr (fun t acc => max (operandTailCode B m t.2) acc) 0

def actualSum (terms : List WeightedOperand) (values : List Nat) : Int :=
  (terms.zipWith (fun t v => t.1 * (v : Int)) values).sum

/-- Exactly one real read per supplied occurrence, in order, including
repeated operands or terms with zero weight. -/
def orderedReads (f : Nat → Nat) (ρ : Nat → Nat) :
    List WeightedOperand → List Nat → Prop
  | [],[] => True
  | t :: terms,v :: values =>
    LowerOperandActual f ρ t.2 v ∧ lowerOperandRead f ρ t.2 = some (some v) ∧
      orderedReads f ρ terms values
  | _,_ => False

def CodeExact : Prop :=
  Primrec₂ weightedResidueCode ∧
  Primrec (fun p : Nat × Nat × List WeightedCode => weightedTailCode p.1 p.2.1 p.2.2) ∧
  (∀ (terms : List WeightedOperand) j,
    weightedResidueCode (terms.map encodeWeighted) j = weightedResidue terms j) ∧
  (∀ (B m : Nat) (terms : List WeightedOperand),
    weightedTailCode B m (terms.map encodeWeighted) = weightedTail B m terms)

/-- A mixed signed list of genuine original operands at one raw rank.
No original value, count, residue or successful read is supplied. -/
def ActualWeightedResidue : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (m rank : Nat) (c : Int) (terms : List WeightedOperand) (ρ : Nat → Nat),
      0 < m →
      (∀ t ∈ terms, t.2.rank = rank ∧ properOperand t.2) →
      weightedTailCode B m (terms.map encodeWeighted) ≤ ρ rank →
        ∃ values : List Nat,
          orderedReads f ρ terms values ∧
          Int.ModEq (m : Int) (c + actualSum terms values)
            (c + weightedResidue terms (ρ rank % (2*m)))

def FullMixedSameRankResidue : Prop := CodeExact ∧ ActualWeightedResidue

end LogicLineages.PermittedControl.MixedSameRankResidue
