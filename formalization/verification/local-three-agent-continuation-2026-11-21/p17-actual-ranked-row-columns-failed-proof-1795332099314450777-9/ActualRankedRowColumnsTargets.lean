module
public import LogicLineages.PermittedControl.ActualWeightedReadNormalizationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedRowColumns
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement ActualWeightedReadNormalization
open SelectedNonlinearImageBounds (NonlinearField)

abbrev ValueKey (r : Nat) := Fin r × ValueField
abbrev CountKey (r : Nat) := (NONote × NONote) × Fin r
abbrev RankedRow (r : Nat) := InnerTerminationTargets.Row (ValueKey r) (NONote × NONote) r

def valueOperand (r : Nat) : ValueKey r ↪ LowerOperand where
  toFun key := .ordinary key.1 key.2
  inj' equal := by
    obtain ⟨rank,field⟩ := LowerOperand.ordinary.inj equal
    exact Prod.ext (Fin.ext rank) field

def countOperand (r : Nat) : CountKey r ↪ LowerOperand where
  toFun key := .count key.2 key.1.1 key.1.2
  inj' equal := by
    obtain ⟨rank,lam,mu⟩ := LowerOperand.count.inj equal
    exact Prod.ext (Prod.ext lam mu) (Fin.ext rank)

/-- The two actual charged columns of the original finite row. Linear
raw coordinates, including the zero iterate, carry no charge. -/
noncomputable def rankedRow (r : Nat) (c : Int) (xs : List Read) : RankedRow r := by
  classical
  let weights := groupedWeights xs
  exact
    { value := (Finsupp.comapDomain (valueOperand r) weights
        (valueOperand r).injective.injOn).filter (fun k => NonlinearField k.2)
      count := Finsupp.comapDomain (countOperand r) weights (countOperand r).injective.injOn
      const := c }

def ExactRankedCoefficients : Prop :=
  ∀ (r : Nat) (c : Int) (xs : List Read),
    let row := rankedRow r c xs
    row.const = c ∧
    (∀ k : CountKey r, row.count k = groupedWeights xs (countOperand r k)) ∧
    (∀ k : ValueKey r, NonlinearField k.2 →
      row.value k = groupedWeights xs (valueOperand r k)) ∧
    (∀ k : ValueKey r, ¬ NonlinearField k.2 → row.value k = 0) ∧
    (∀ k : CountKey r, k ∈ row.count.support ↔
      countOperand r k ∈ (groupedWeights xs).support) ∧
    (∀ k : ValueKey r, k ∈ row.value.support ↔
      NonlinearField k.2 ∧ valueOperand r k ∈ (groupedWeights xs).support)

def WitnessesColumn (f : Nat → Nat) (ρ : Nat → Nat) (out : List Read)
    (key : LowerOperand) (weight : Int) : Prop :=
  ∃ v : Nat, (((weight,key),v) : Read) ∈ out ∧
    LowerOperandActual f ρ key v ∧ lowerOperandRead f ρ key = some (some v)

def IsInRankedColumn {r : Nat} (row : RankedRow r) (read : Read) : Prop :=
  match read.1.2 with
  | .coordinate _ => True
  | .ordinary n F =>
      NonlinearField F → ∃ rank : Fin r,
        rank.1 = n ∧ (rank,F) ∈ row.value.support ∧ row.value (rank,F) = read.1.1
  | .count n lam mu =>
      ∃ rank : Fin r,
        rank.1 = n ∧ ((lam,mu),rank) ∈ row.count.support ∧
        row.count ((lam,mu),rank) = read.1.1

/-- Every charged support key is supplied by the true normalized read
at its literal original ordinal field and rank, and conversely every
retained charged read has that finite-rank support key. -/
def ExactRankedReads : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (r : Nat) (c : Int) (xs : List Read),
    liftedReads f ρ xs → (∀ read ∈ xs, read.1.2.rank < r) →
    let row := rankedRow r c xs
    ∃ out : List Read, normalizeReads f ρ xs = some out ∧
      liftedReads f ρ out ∧ readSum xs = readSum out ∧
      (∀ k ∈ row.count.support, WitnessesColumn f ρ out (countOperand r k) (row.count k)) ∧
      (∀ k ∈ row.value.support, WitnessesColumn f ρ out (valueOperand r k) (row.value k)) ∧
      ∀ read ∈ out, IsInRankedColumn row read

def FullActualRankedRowColumns : Prop := ExactRankedCoefficients ∧ ExactRankedReads

end LogicLineages.PermittedControl.ActualRankedRowColumns
