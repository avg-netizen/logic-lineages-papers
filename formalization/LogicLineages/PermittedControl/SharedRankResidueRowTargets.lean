module
public import LogicLineages.PermittedControl.MixedRankNamedResidueRowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SharedRankResidueRow
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand encodeWeighted weightedTailCode properOperand
  orderedReads actualSum)
open MixedRankResidue (rankSupport rankSupportCode residueVector residueVectorCode)
open RankResidueChoices (Slot namedSlots choices)
open MixedNamedResidueRow (keep)
open MixedRankNamedResidueRow (RawArgs rawArgs rowFrom toVector clauseCode)

abbrev SourceRow := Nat × Int × List WeightedOperand
abbrev Layout := List Slot

def encodeRow (r : SourceRow) : RawArgs := rawArgs r.1 r.2.1 r.2.2

def commonLayout (rows : List SourceRow) : Layout :=
  namedSlots (rankSupport (rows.flatMap (fun r => r.2.2)))

def commonLayoutCode (rows : List RawArgs) : Layout :=
  namedSlots (rankSupportCode (rows.flatMap (fun r => r.2.2)))

def requests (layout : Layout) : List NamedOperand :=
  layout.map (fun s => (s.1,.coordinate s.2))

noncomputable def formula (layout : Layout) (r : SourceRow) : NormalForm.Formula :=
  rowFrom r.1 (fun cell => keep r.1 (r.2.1 + residueVector r.2.2 (toVector cell)))
    (choices r.1 layout)

def formulaCode (layout : Layout) (r : RawArgs) : Nat :=
  (choices r.1 layout).foldr (fun cell tail =>
    if keep r.1 (r.2.1 + residueVectorCode r.2.2 (toVector cell)) then
      6 * Nat.pair (clauseCode r.1 cell) tail + 5 else tail) 1

def prepareCode (p : Layout × RawArgs) : Option (List NamedCode × Nat) :=
  if p.2.1 = 0 then none else
    some (p.1.map (fun s => (s.1,(0,s.2,(0,0,0,0)))),formulaCode p.1 p.2)

def CodeExact : Prop :=
  Primrec commonLayoutCode ∧ Primrec prepareCode ∧
  (∀ rows : List SourceRow, commonLayoutCode (rows.map encodeRow) = commonLayout rows) ∧
  (∀ p : Layout × RawArgs, p.2.1 = 0 → prepareCode p = none) ∧
  ∀ (layout : Layout) (r : SourceRow), 0 < r.1 →
    prepareCode (layout,encodeRow r) = some ((requests layout).map encodeRequest,(formula layout r).encode)

def CommonLayoutExact : Prop :=
  ∀ rows : List SourceRow,
    ((commonLayout rows).map Prod.fst).Nodup ∧ ((commonLayout rows).map Prod.snd).Nodup ∧
    (∀ s ∈ commonLayout rows, 0 < s.1) ∧
    ∀ rank : Nat, rank ∈ (commonLayout rows).map Prod.snd ↔
      ∃ r ∈ rows, rank ∈ rankSupport r.2.2

def FormulaSupport : Prop :=
  ∀ (layout : Layout) (r : SourceRow),
    PlainPreparedFormula (formula layout r) ∧
    ∀ name ∈ (formula layout r).variables, name ∈ (requests layout).map Prod.fst

/-- Larger layouts change names only. Values, proper-field guards and the
effective tail remain those of the original unpadded row. -/
def ActualRowAtLayout : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (layout : Layout) (r : SourceRow) (ρ : Nat → Nat),
    0 < r.1 →
    (∀ rank ∈ rankSupport r.2.2, rank ∈ layout.map Prod.snd) →
    (∀ t ∈ r.2.2, properOperand t.2) →
    (∀ rank ∈ rankSupport r.2.2, weightedTailCode B r.1 (r.2.2.map encodeWeighted) ≤ ρ rank) →
    ∃ values : List Nat, orderedReads f ρ r.2.2 values ∧
      ∀ ν : Nat → Nat, (∀ s ∈ layout, ν s.1 = ρ s.2) →
        ((formula layout r).eval ν ↔ (r.1 : Int) ∣ r.2.1 + actualSum r.2.2 values)

def FullSharedRankResidueRow : Prop := CodeExact ∧ CommonLayoutExact ∧ FormulaSupport ∧ ActualRowAtLayout

end LogicLineages.PermittedControl.SharedRankResidueRow
