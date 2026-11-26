module
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets
public import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLinearLowerTable
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand lowerOperandRead PreparedTableTied)
open MixedSameRankResidue (WeightedOperand)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowSliceValue (valueAt)
open ActualMixedRowLeadingAnnotations (LinearOperand)

def TopLinear (top : Nat) (rows : List Row) : Prop :=
  ∀ row ∈ rows, ∀ t ∈ row.2.2, t.2.rank ≤ top ∧
    (t.2.rank = top → LinearOperand t.2)

def lowerTable (top : Nat) (rows : List Row) : List LowerOperand :=
  ((rows.flatMap (fun row => row.2.2.map Prod.snd)).filter (fun op => decide (op.rank < top)))

def Live (f ρ : Nat → Nat) (ops : List LowerOperand) : Prop :=
  ∀ op ∈ ops, ∃ v : Nat, lowerOperandRead f ρ op = some (some v)

private theorem hasIndex {op : LowerOperand} {ops : List LowerOperand} (h : op ∈ ops) :
    ∃ i : Nat, ∃ hi : i < ops.length, ops[i] = op :=
  List.mem_iff_getElem.mp h

/-- The table retains every original lower occurrence in source order.
If exactly equal operands repeat, a reference may use any matching
slot; the actual reader forces every such slot to agree. -/
noncomputable def slot (ops : List LowerOperand) (op : LowerOperand) : Nat :=
  @dite Nat (op ∈ ops) (Classical.propDecidable _)
    (fun h => (Classical.choose (hasIndex h))+1) (fun _ => 0)

noncomputable def nameAt (top : Nat) (ops : List LowerOperand) (op : LowerOperand) : Nat :=
  if op.rank = top then 0 else slot ops op

noncomputable def preparedRow (top : Nat) (ops : List LowerOperand) (r : Row) : NormalForm.Row :=
  (r.2.1,r.2.2.map (fun t => (t.1,.variable (nameAt top ops t.2))))

/-- Undefined slots outside the true table are irrelevant. In-range
slots are certified against the real exact read, without using defaults. -/
noncomputable def assignment (f ρ : Nat → Nat) (ops : List LowerOperand) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k+1 => ((ops[k]?).bind (fun op => (lowerOperandRead f ρ op).join)).getD 0

def ExactLinearLowerTable : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (rows : List Row),
    let ops := lowerTable top rows
    (∀ op ∈ ops, op.rank < top) ∧
    (Live f ρ ops ↔ ∃ ν : Nat → Nat, PreparedTableTied f top ρ ops ν) ∧
    (Live f ρ ops → PreparedTableTied f top ρ ops (assignment f ρ ops)) ∧
    ∀ (z : Nat) (snap : Snapshot),
      actualRows f (Function.update ρ top z) rows snap → Live f ρ ops

def ExactLinearPreparedRow : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (rows : List Row), TopLinear top rows →
  ∀ row ∈ rows,
    let ops := lowerTable top rows
    let lowered := preparedRow top ops row
    (∀ n ∈ NormalForm.rowVariables lowered, n ≤ ops.length) ∧
    ∀ (ν : Nat → Nat), PreparedTableTied f top ρ ops ν →
      ∀ (z : Nat) (v : Int),
        valueAt f (Function.update ρ top z) row.2.1 row.2.2 v ↔
          NormalForm.rowValue lowered (Function.update ν 0 z) = v

def FullOriginalMatrixLinearLowerTable : Prop := ExactLinearLowerTable ∧ ExactLinearPreparedRow

end LogicLineages.PermittedControl.OriginalMatrixLinearLowerTable
