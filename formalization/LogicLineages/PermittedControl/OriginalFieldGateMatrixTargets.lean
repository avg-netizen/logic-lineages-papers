module
public import LogicLineages.PermittedControl.OriginalNaturalFieldGatesTargets
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalFieldGateMatrix
open OrdinalComparison PreparedProjection
open OriginalNaturalFieldGates (Gate Valuation)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

def equalityRow (operand : LowerOperand) (output : Nat) : Row :=
  (.equalZero,0,[(-1,.coordinate output),(1,operand)])

def zeroRow (output : Nat) : Row :=
  (.equalZero,0,[(-1,.coordinate output)])

def identityShapeRow (mu : NONote) : Row :=
  let n := rawNoteEncode mu.1
  (.equalZero,if terminalScanGuard (n,n) then 0 else 1,[])

noncomputable def identityAffordRow (mu : NONote) (source : Nat) : Row :=
  (.nonnegative,-(actualOrdinalNorm mu.1.repr : Int),[(1,.coordinate source)])

noncomputable def rows : Gate → List Row
  | .iterate steps s o => [equalityRow (.ordinary s (.iterate steps)) o]
  | .entry (.proper lam mu) s o => [equalityRow (.ordinary s (.entry 0 lam mu)) o]
  | .count (.proper lam mu) s o => [equalityRow (.count s lam mu) o]
  | .entry (.identity mu) s o =>
      [identityShapeRow mu,identityAffordRow mu s,equalityRow (.coordinate s) o]
  | .count (.identity mu) s o =>
      [identityShapeRow mu,identityAffordRow mu s,zeroRow o]

/-- Literal passing signed snapshot at the same source/output valuation.
It is not a supplied successful read or replacement valuation. -/
noncomputable def passing (θ : Valuation) : Gate → Snapshot
  | .entry (.identity mu) s _ | .count (.identity mu) s _ =>
      [(0,true),((θ s : Int)-(actualOrdinalNorm mu.1.repr : Int),true),(0,true)]
  | _ => [(0,true)]

noncomputable def rowsList (gates : List Gate) : List Row := gates.flatMap rows
noncomputable def passingList (θ : Valuation) (gates : List Gate) : Snapshot :=
  gates.flatMap (passing θ)

def ExactOriginalFieldRow : Prop :=
  ∀ (f : Nat → Nat) (θ : Valuation) (g : Gate),
    actualRows f θ (rows g) (passing θ g) ↔ g.graph f θ

def ExactOriginalFieldList : Prop :=
  ∀ (f : Nat → Nat) (θ : Valuation) (gates : List Gate),
    (rowsList gates).length = (passingList θ gates).length ∧
      (actualRows f θ (rowsList gates) (passingList θ gates) ↔ ∀ g ∈ gates, g.graph f θ)

def FullOriginalFieldGateMatrix : Prop :=
  ExactOriginalFieldRow ∧ ExactOriginalFieldList

end LogicLineages.PermittedControl.OriginalFieldGateMatrix
