module
public import LogicLineages.PermittedControl.MixedSameRankResidueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.MixedNamedResidueRow
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open CountCongruenceNamedRow (requests residueAtom residueAtomCode)
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted weightedResidue
  weightedResidueCode weightedTailCode properOperand orderedReads actualSum)

abbrev RawArgs := Nat × Nat × Int × List WeightedCode

def rawArgs (m rank : Nat) (c : Int) (terms : List WeightedOperand) : RawArgs :=
  (m,rank,c,terms.map encodeWeighted)

def keep (m : Nat) (value : Int) : Bool := decide (value.natAbs % m = 0)

def rowFrom (m : Nat) (retain : Nat → Bool) (indices : List Nat) : NormalForm.Formula :=
  indices.foldr (fun j tail => if retain j then .disjunction (residueAtom m j) tail else tail)
    .falsity

noncomputable def row (m : Nat) (c : Int) (terms : List WeightedOperand) : NormalForm.Formula :=
  rowFrom m (fun j => keep m (c + weightedResidue terms j)) (List.range (2*m))

def rowCode (m : Nat) (c : Int) (terms : List WeightedCode) : Nat :=
  (List.range (2*m)).foldr (fun j tail =>
    if keep m (c + weightedResidueCode terms j) then
      6 * Nat.pair (residueAtomCode m j) tail + 5 else tail) 1

/-- Original radix-six code and the singleton raw-coordinate request.
Only canonical operand codes are interpreted, and modulus zero is rejected. -/
def prepareCode (q : RawArgs) : Option (List NamedCode × Nat) :=
  let (m,rank,c,terms) := q
  if m = 0 then none else some ([(1,(0,rank,(0,0,0,0)))],rowCode m c terms)

def CodeExact : Prop :=
  Primrec prepareCode ∧
  (∀ q : RawArgs, q.1 = 0 → prepareCode q = none) ∧
  ∀ (m rank : Nat) (c : Int) (terms : List WeightedOperand), 0 < m →
    prepareCode (rawArgs m rank c terms) =
      some ((requests rank).map encodeRequest,(row m c terms).encode)

def ShapeAndSupport : Prop :=
  ∀ (m rank : Nat) (c : Int) (terms : List WeightedOperand),
    let rs := requests rank
    let p := row m c terms
    PlainPreparedFormula p ∧ (∀ r ∈ rs, 0 < r.1) ∧ (rs.map Prod.fst).Nodup ∧
      ∀ i ∈ p.variables, i ∈ rs.map Prod.fst

/-- At the common original raw coordinate, every weighted occurrence has its
own actual closed read. The formula names only that coordinate. -/
def ActualNamedRow : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m rank : Nat) (c : Int) (terms : List WeightedOperand) (ρ : Nat → Nat),
    0 < m → (∀ t ∈ terms, t.2.rank = rank ∧ properOperand t.2) →
    weightedTailCode B m (terms.map encodeWeighted) ≤ ρ rank →
    ∃ values : List Nat, orderedReads f ρ terms values ∧
      ∀ ν : Nat → Nat, ν 1 = ρ rank →
        ((row m c terms).eval ν ↔ (m : Int) ∣ c + actualSum terms values)

def FullMixedNamedResidueRow : Prop := CodeExact ∧ ShapeAndSupport ∧ ActualNamedRow

end LogicLineages.PermittedControl.MixedNamedResidueRow
