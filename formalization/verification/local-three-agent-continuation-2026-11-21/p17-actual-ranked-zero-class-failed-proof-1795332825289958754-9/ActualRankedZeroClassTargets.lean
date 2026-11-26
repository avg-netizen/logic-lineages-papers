module
public import LogicLineages.PermittedControl.ActualRankedRowColumnsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedZeroClass
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open ActualZeroClassReplacement ActualWeightedReadNormalization ActualRankedRowColumns

/-- Retain the original operand and its own annotation. Equality of
lowered prefix target notes never identifies source count keys. -/
def classLedger (f : Nat → Nat) (C : Nat) :
    List Read → List Annotation → List (Read × Annotation)
  | rd::xs,ann::annotations =>
      if fullValue f ann = some C then
        (rd,ann) :: classLedger f C xs annotations
      else classLedger f C xs annotations
  | _,_ => []

def classReads (f : Nat → Nat) (C : Nat) (xs : List Read) (annotations : List Annotation) :
    List Read := (classLedger f C xs annotations).map Prod.fst

def leadingWeight (rd : Read) : Int :=
  match rd.1.2 with
  | .coordinate _ => 0
  | .ordinary _ _ => 2 * rd.1.1
  | .count _ _ _ => rd.1.1

def finiteClassKey (r : Nat) : LowerOperand → Option (ValueKey r ⊕ CountKey r)
  | .coordinate _ => none
  | .ordinary n F => if h : n < r then some (.inl (⟨n,h⟩,F)) else none
  | .count n lam mu => if h : n < r then some (.inr ((lam,mu),⟨n,h⟩)) else none

noncomputable def finiteClassColumns (r : Nat) : List Read → Finset (ValueKey r) × Finset (CountKey r)
  | [] => (∅,∅)
  | rd::xs => by
      classical
      let tail := finiteClassColumns r xs
      exact match finiteClassKey r rd.1.2 with
        | none => tail
        | some (.inl k) => (insert k tail.1,tail.2)
        | some (.inr k) => (tail.1,insert k tail.2)

def ExactClassSelection : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (xs : List Read)
    (annotations : List Annotation),
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    let ledger := classLedger f C xs annotations
    let selected := classReads f C xs annotations
    selected.Sublist xs ∧
    (∀ item ∈ ledger,
      ActualAnnotation f ρ item.1.1 item.1.2 item.2 ∧ fullValue f item.2 = some C) ∧
    (∀ rd ∈ selected, NonlinearOperand rd.1.2) ∧
    (selected ≠ [] ↔ C ∈ fullValues f annotations) ∧
    (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 =
      (selected.map leadingWeight).sum

/-- The selected C comes from the actual full values of the same
normalized source row. The finite columns supply the exact weighted
zero-class criterion over the original count interval keys. -/
def ExactRankedClass : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (r : Nat) (c : Int)
    (raw xs : List Read) (annotations : List Annotation) (C : Nat),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    let row := rankedRow r c raw
    let selected := classReads f C xs annotations
    let columns := finiteClassColumns r selected
    columns.1 ⊆ row.value.support ∧ columns.2 ⊆ row.count.support ∧
    (columns.1.Nonempty ∨ columns.2.Nonempty) ∧
    (∀ k : ValueKey r, k ∈ columns.1 ↔ ∃ rd ∈ selected, rd.1.2 = valueOperand r k) ∧
    (∀ k : CountKey r, k ∈ columns.2 ↔ ∃ rd ∈ selected, rd.1.2 = countOperand r k) ∧
    (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 =
      2 * (∑ k ∈ columns.1, row.value k) + ∑ k ∈ columns.2, row.count k

def FullActualRankedZeroClass : Prop := ExactClassSelection ∧ ExactRankedClass

end LogicLineages.PermittedControl.ActualRankedZeroClass
