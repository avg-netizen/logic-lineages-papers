module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawLow
open HeterogeneousSignedMatrixSlice (RawRow RawResult)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (sliceClause sliceFamily strips coordinates dimension)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily names)

/-- A row is kept only after a genuine hit. Invalid and missed reads
both reject the clause, without converting either to a false row. -/
def takeHit (r : RawResult × Bool) : Option RawBitRow :=
  r.1.2.bind fun payload =>
    payload.map fun out => ((r.1.1,out),r.2)

def joinClause (head : Option RawBitRow) (tail : Option (List RawBitRow)) :
    Option (List RawBitRow) :=
  head.bind fun row => tail.map (List.cons row)

abbrev ClauseArgs := Nat × Nat × List RawBitRow
abbrev FamilyArgs := Nat × Nat × RawFamily
abbrev Branch := Nat × RawFamily

noncomputable def sliceOne (f : Nat → Nat) (p : Nat × Nat × RawBitRow) : Option RawBitRow :=
  takeHit ((p.2.2.1.1,
    SignedRowCoordinateSlice.sliceCode f (p.1,p.2.1,p.2.2.1.2.1,p.2.2.1.2.2)),p.2.2.2)

noncomputable def clauseCode (f : Nat → Nat) (p : ClauseArgs) : Option (List RawBitRow) :=
  p.2.2.foldr (fun row tail => joinClause (sliceOne f (p.1,p.2.1,row)) tail) (some [])

noncomputable def familyCode (f : Nat → Nat) (p : FamilyArgs) : RawFamily :=
  p.2.2.filterMap (fun c => clauseCode f (p.1,p.2.1,c))

noncomputable def stripsCode (f : Nat → Nat) (p : FamilyArgs) : List Branch :=
  (List.range p.2.1).map (fun a => (a,familyCode f (p.1,a,p.2.2)))

def ExactRawLowCode : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (clauseCode f) ∧
    Computable (familyCode f) ∧ Computable (stripsCode f))

def ExactRawLowCalibration : Prop :=
  (∀ (f : Nat → Nat) (name a : Nat) (clause : List BitRow),
    clauseCode f (name,a,clause.map encodeBitRow) =
      (sliceClause f name a clause).map (List.map encodeBitRow)) ∧
  (∀ (f : Nat → Nat) (name a : Nat) (family : Family),
    familyCode f (name,a,encodeFamily family) = encodeFamily (sliceFamily f name a family)) ∧
  ∀ (f : Nat → Nat) (name bound : Nat) (family : Family),
    stripsCode f (name,bound,encodeFamily family) =
      (strips f name bound family).map (fun br => (br.1,encodeFamily br.2))

def ExactRawLowDimension : Prop :=
  ∀ (f : Nat → Nat) (name bound : Nat) (family : Family),
    name ∈ names (encodeFamily family) →
    ∀ br ∈ stripsCode f (name,bound,encodeFamily family),
      (names br.2).toFinset ⊆ (names (encodeFamily family)).toFinset.erase name ∧
      (names br.2).length < (names (encodeFamily family)).length

def FullActualBitFamilyRawLow : Prop :=
  ExactRawLowCode ∧ ExactRawLowCalibration ∧ ExactRawLowDimension

end LogicLineages.PermittedControl.ActualBitFamilyRawLow
