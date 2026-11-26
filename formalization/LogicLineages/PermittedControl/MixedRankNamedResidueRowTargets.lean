module
public import LogicLineages.PermittedControl.RankResidueChoicesTargets
public import LogicLineages.PermittedControl.MixedNamedResidueRowTargets
public import LogicLineages.PermittedControl.MixedRankResidueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankNamedResidueRow
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted weightedTailCode properOperand
  orderedReads actualSum)
open MixedRankResidue (Residues rankSupport rankSupportCode residueVector residueVectorCode)
open RankResidueChoices (Slot Cell namedSlots choices)
open MixedNamedResidueRow (keep)

abbrev RawArgs := Nat × Int × List WeightedCode

def rawArgs (m : Nat) (c : Int) (terms : List WeightedOperand) : RawArgs :=
  (m,c,terms.map encodeWeighted)

def slots (terms : List WeightedOperand) : List Slot := namedSlots (rankSupport terms)

def requests (terms : List WeightedOperand) : List NamedOperand :=
  (slots terms).map (fun s => (s.1,.coordinate s.2))

def toVector (cell : Cell) : Residues := cell.map (fun e => (e.2.1,e.2.2))

def atom (m name j : Nat) : NormalForm.Formula :=
  .atom (.divisible (2*m-1) (-(j : Int),[(1,.variable name)]))

def atomCode (m name j : Nat) : Nat :=
  let p : NormalForm.Code.AtomData := (1,2*m-1,-(j : Int),[(1,(0,name,0,0))])
  6 * Encodable.encode p + 2

def clause (m : Nat) (cell : Cell) : NormalForm.Formula :=
  cell.foldr (fun e tail => .conjunction (atom m e.1 e.2.2) tail) .truth

def clauseCode (m : Nat) (cell : Cell) : Nat :=
  cell.foldr (fun e tail => 6 * Nat.pair (atomCode m e.1 e.2.2) tail + 4) 0

def rowFrom (m : Nat) (retain : Cell → Bool) (cells : List Cell) : NormalForm.Formula :=
  cells.foldr (fun cell tail => if retain cell then .disjunction (clause m cell) tail else tail) .falsity

noncomputable def row (m : Nat) (c : Int) (terms : List WeightedOperand) : NormalForm.Formula :=
  rowFrom m (fun cell => keep m (c + residueVector terms (toVector cell))) (choices m (slots terms))

def rowCode (m : Nat) (c : Int) (terms : List WeightedCode) : Nat :=
  (choices m (namedSlots (rankSupportCode terms))).foldr (fun cell tail =>
    if keep m (c + residueVectorCode terms (toVector cell)) then
      6 * Nat.pair (clauseCode m cell) tail + 5 else tail) 1

def prepareCode (q : RawArgs) : Option (List NamedCode × Nat) :=
  let (m,c,terms) := q
  if m = 0 then none else
    some ((namedSlots (rankSupportCode terms)).map (fun s => (s.1,(0,s.2,(0,0,0,0)))),
      rowCode m c terms)

def CodeExact : Prop :=
  Primrec prepareCode ∧ (∀ q : RawArgs, q.1 = 0 → prepareCode q = none) ∧
  ∀ (m : Nat) (c : Int) (terms : List WeightedOperand), 0 < m →
    prepareCode (rawArgs m c terms) = some ((requests terms).map encodeRequest,(row m c terms).encode)

def ShapeAndSupport : Prop :=
  ∀ (m : Nat) (c : Int) (terms : List WeightedOperand),
    let rs := requests terms
    let p := row m c terms
    PlainPreparedFormula p ∧ (∀ r ∈ rs, 0 < r.1) ∧ (rs.map Prod.fst).Nodup ∧
      ∀ i ∈ p.variables, i ∈ rs.map Prod.fst

/-- Every used raw rank receives its original value in the same valuation.
All actual weighted reads are outputs under the one effective tail. -/
def ActualNamedRow : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m : Nat) (c : Int) (terms : List WeightedOperand) (ρ : Nat → Nat),
    0 < m → (∀ t ∈ terms, properOperand t.2) →
    (∀ r ∈ rankSupport terms, weightedTailCode B m (terms.map encodeWeighted) ≤ ρ r) →
    ∃ values : List Nat, orderedReads f ρ terms values ∧
      ∀ ν : Nat → Nat, (∀ s ∈ slots terms, ν s.1 = ρ s.2) →
        ((row m c terms).eval ν ↔ (m : Int) ∣ c + actualSum terms values)

def FullMixedRankNamedResidueRow : Prop := CodeExact ∧ ShapeAndSupport ∧ ActualNamedRow

end LogicLineages.PermittedControl.MixedRankNamedResidueRow
