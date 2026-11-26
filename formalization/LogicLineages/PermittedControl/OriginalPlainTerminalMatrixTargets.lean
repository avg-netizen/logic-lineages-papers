module
public import LogicLineages.PermittedControl.OriginalMixedTerminalTestTargets
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPlainTerminalMatrix
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

def atomTest : NormalForm.Atom → SignedRowGuardedTest.Test
  | .nonnegative _ => .nonnegative
  | .divisible m _ => .congruence (m + 1)

/-- Literal occurrence translation. The source admission predicate rules
out nonlinear summands; their names alone are not their values. -/
def atomRow (a : NormalForm.Atom) : Row :=
  (atomTest a,a.row.1,a.row.2.map (fun t => (t.1,.coordinate t.2.name)))

def rows (p : NormalForm.Formula) : List Row := (LinearRows.atoms p).map atomRow

def atomAnswer (θ : Nat → Nat) : NormalForm.Atom → Bool
  | .nonnegative r => decide (0 ≤ NormalForm.rowValue r θ)
  | .divisible m r => decide (NormalForm.rowValue r θ % ((m + 1 : Nat) : Int) = 0)

def snapshot (θ : Nat → Nat) (p : NormalForm.Formula) : Snapshot :=
  (LinearRows.atoms p).map (fun a => (NormalForm.rowValue a.row θ,atomAnswer θ a))

/-- Read both subtrees, even when the first bit would short circuit the
Boolean connective. Each duplicate atom keeps its own original position. -/
def readBits : NormalForm.Formula → List Bool → Option (Bool × List Bool)
  | .truth, bits => some (true,bits)
  | .falsity, bits => some (false,bits)
  | .atom _, [] => none
  | .atom _, b :: rest => some (b,rest)
  | .negative p, bits => do
      let (b,rest) ← readBits p bits
      pure (!b,rest)
  | .conjunction p q, bits => do
      let (b,mid) ← readBits p bits
      let (c,rest) ← readBits q mid
      pure (b && c,rest)
  | .disjunction p q, bits => do
      let (b,mid) ← readBits p bits
      let (c,rest) ← readBits q mid
      pure (b || c,rest)

def accepts (p : NormalForm.Formula) (positive : Bool) (values : Snapshot) : Prop :=
  readBits p (values.map Prod.snd) = some (positive,[])

def ExactPlainTerminalSnapshot : Prop :=
  ∀ (f θ : Nat → Nat) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p → ∀ values : Snapshot,
      actualRows f θ (rows p) values ↔ values = snapshot θ p

def ExactPlainTerminalSuffix : Prop :=
  ∀ (f θ : Nat → Nat) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p → ∀ positive : Bool,
      ((OriginalMixedTerminalTest.Test.rows p).atPolarity positive θ) ↔
        ∃ values : Snapshot, actualRows f θ (rows p) values ∧ accepts p positive values

def FullOriginalPlainTerminalMatrix : Prop := ExactPlainTerminalSnapshot ∧ ExactPlainTerminalSuffix

end LogicLineages.PermittedControl.OriginalPlainTerminalMatrix
