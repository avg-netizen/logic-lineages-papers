module
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPreparedSlotAppend
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm PreparedProjection

abbrev Packet := List LowerOperand × Formula

/-- Zero is the one raw coordinate being varied, not a table slot.
Only positive names in the appended packet acquire an offset. -/
def shiftName (d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => d + (n + 1)

def view (d : Nat) (ν : Nat → Nat) : Nat → Nat := fun n => ν (shiftName d n)

def shiftSummand (d : Nat) : Summand → Summand
  | .variable i => .variable (shiftName d i)
  | .phi i e => .phi (shiftName d i) e
  | .hyperPhi i e h => .hyperPhi (shiftName d i) e h

def shiftRow (d : Nat) (r : Row) : Row :=
  (r.1,r.2.map fun t => (t.1,shiftSummand d t.2))

def shiftAtom (d : Nat) : Atom → Atom
  | .nonnegative r => .nonnegative (shiftRow d r)
  | .divisible m r => .divisible m (shiftRow d r)

def shift (d : Nat) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (shiftAtom d a)
  | .negative p => .negative (shift d p)
  | .conjunction p q => .conjunction (shift d p) (shift d q)
  | .disjunction p q => .disjunction (shift d p) (shift d q)

def append (left right : Packet) : Packet :=
  (left.1 ++ right.1,.conjunction left.2 (shift left.1.length right.2))

/-- Merge only the lower table addresses. The assembled reserved
coordinate is always the left assignment's zeroth value. -/
def merge (d : Nat) (ν₁ ν₂ : Nat → Nat) (n : Nat) : Nat :=
  if n ≤ d then ν₁ n else ν₂ (n-d)

def ExactSlotShift : Prop :=
  (∀ (d : Nat) (ν : Nat → Nat), view d ν 0 = ν 0) ∧
  ∀ (d : Nat) (p : Formula),
    (shift d p).variables = p.variables.map (shiftName d) ∧
    (PlainPreparedFormula p →
      PlainPreparedFormula (shift d p) ∧ ∀ (ν : Nat → Nat),
        ((shift d p).eval ν ↔ p.eval (view d ν)))

def ExactAppendedReads : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (left right : List LowerOperand),
    (∀ (j : Nat) (hj : j < left.length),
      ∃ hab : j < (left ++ right).length,
        (left ++ right)[j] = left[j] ∧
        lowerOperandRead f ρ ((left ++ right)[j]) = lowerOperandRead f ρ left[j]) ∧
    (∀ (j : Nat) (hj : j < right.length),
      ∃ hab : left.length+j < (left ++ right).length,
        (left ++ right)[left.length+j] = right[j] ∧
        lowerOperandRead f ρ ((left ++ right)[left.length+j]) = lowerOperandRead f ρ right[j]) ∧
    (∀ (ν : Nat → Nat),
      (PreparedTableTied f top ρ (left ++ right) ν ↔
        PreparedTableTied f top ρ left ν ∧ PreparedTableTied f top ρ right (view left.length ν))) ∧
    ∀ (ν₁ ν₂ : Nat → Nat),
      PreparedTableTied f top ρ left ν₁ → PreparedTableTied f top ρ right ν₂ →
      PreparedTableTied f top ρ (left ++ right) (merge left.length ν₁ ν₂)

def ExactPreparedAppend : Prop :=
  ∀ (left right : Packet), PreparedInput left.1 left.2 → PreparedInput right.1 right.2 →
    let both := append left right
    PreparedInput both.1 both.2 ∧
    (∀ (ν : Nat → Nat), both.2.eval ν ↔ left.2.eval ν ∧ right.2.eval (view left.1.length ν)) ∧
    ∀ (ν₁ ν₂ : Nat → Nat), ν₁ 0 = ν₂ 0 →
      (both.2.eval (merge left.1.length ν₁ ν₂) ↔ left.2.eval ν₁ ∧ right.2.eval ν₂)

def FullActualPreparedSlotAppend : Prop :=
  ExactSlotShift ∧ ExactAppendedReads ∧ ExactPreparedAppend

end LogicLineages.PermittedControl.ActualPreparedSlotAppend
