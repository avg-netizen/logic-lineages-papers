module
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrix
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (encodeWeighted weightedTailCode properOperand orderedReads actualSum)
open MixedRankResidue (rankSupport)
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow Layout encodeRow commonLayout commonLayoutCode requests)

def conjoinCode (layout : Layout) (r : RawArgs) (tail : Option Nat) : Option Nat := do
  let head ← SharedRankResidueRow.prepareCode (layout,r)
  let rest ← tail
  pure (6 * Nat.pair head.2 rest + 4)

def compileCode (rows : List RawArgs) : Option (List NamedCode × Nat) :=
  let layout := commonLayoutCode rows
  (rows.foldr (conjoinCode layout) (some 0)).map (fun code =>
    (layout.map (fun s => (s.1,(0,s.2,(0,0,0,0)))),code))

noncomputable def formulaAtLayout (layout : Layout) (rows : List SourceRow) : NormalForm.Formula :=
  rows.foldr (fun r tail => .conjunction (SharedRankResidueRow.formula layout r) tail) .truth

noncomputable def formula (rows : List SourceRow) : NormalForm.Formula := formulaAtLayout (commonLayout rows) rows

def rowTail (B : Nat) (r : SourceRow) : Nat := weightedTailCode B r.1 (r.2.2.map encodeWeighted)

def commonTail (B : Nat) (rows : List SourceRow) : Nat :=
  rows.foldr (fun r tail => max (rowTail B r) tail) 0

def commonTailCode (B : Nat) (rows : List RawArgs) : Nat :=
  rows.foldr (fun r tail => max (weightedTailCode B r.1 r.2.2) tail) 0

/-- The same raw valuation is used by every original row. The outer and
inner lists preserve all row and operand occurrences in their source order. -/
def actualRows (f ρ : Nat → Nat) : List SourceRow → List (List Nat) → Prop
  | [],[] => True
  | r :: rows,values :: rest =>
    orderedReads f ρ r.2.2 values ∧ ((r.1 : Int) ∣ r.2.1 + actualSum r.2.2 values) ∧
      actualRows f ρ rows rest
  | _,_ => False

def CodeExact : Prop :=
  Primrec compileCode ∧
  (∀ rows : List RawArgs, compileCode rows = none ↔ ∃ r ∈ rows, r.1 = 0) ∧
  ∀ rows : List SourceRow, (∀ r ∈ rows, 0 < r.1) →
    compileCode (rows.map encodeRow) = some ((requests (commonLayout rows)).map encodeRequest,(formula rows).encode)

def TailExact : Prop :=
  Primrec₂ commonTailCode ∧
  (∀ (B : Nat) (rows : List SourceRow), commonTailCode B (rows.map encodeRow) = commonTail B rows) ∧
  ∀ (B : Nat) (rows : List SourceRow), ∀ r ∈ rows, rowTail B r ≤ commonTail B rows

def FormulaSupport : Prop :=
  ∀ rows : List SourceRow, PlainPreparedFormula (formula rows) ∧
    ∀ i ∈ (formula rows).variables, i ∈ (requests (commonLayout rows)).map Prod.fst

def ActualConjunction : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (rows : List SourceRow) (ρ ν : Nat → Nat),
    (∀ r ∈ rows, 0 < r.1 ∧ ∀ t ∈ r.2.2, properOperand t.2) →
    (∀ r ∈ rows, ∀ rank ∈ rankSupport r.2.2, rowTail B r ≤ ρ rank) →
    (∀ s ∈ commonLayout rows, ν s.1 = ρ s.2) →
    ((formula rows).eval ν ↔ ∃ values : List (List Nat), actualRows f ρ rows values)

def FullSignedCongruenceMatrix : Prop := CodeExact ∧ TailExact ∧ FormulaSupport ∧ ActualConjunction

end LogicLineages.PermittedControl.SignedCongruenceMatrix
