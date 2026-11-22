module
public import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyTargets
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyLowSlices
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds zipBits)
open ActualGuardedResidualBitFamily (Family Holds)
open HeterogeneousSignedMatrixSlice (Row RowResult HitRows sliceRows)
open OriginalMatrixLowDimension (supportSet)

def originalRows (clause : List BitRow) : List Row := clause.map Prod.fst

def wantedBits (clause : List BitRow) : List Bool := clause.map Prod.snd

def extractHits : List RowResult → Option (List Row)
  | [] => some []
  | (test,some (some (b,terms)))::tail => (extractHits tail).map (fun rs => (test,b,terms)::rs)
  | _ => none

noncomputable def sliceClause (f : Nat → Nat) (name a : Nat) (clause : List BitRow) : Option (List BitRow) :=
  (extractHits (sliceRows f name a (originalRows clause))).map (fun rs => zipBits rs (wantedBits clause))

noncomputable def sliceFamily (f : Nat → Nat) (name a : Nat) (family : Family) : Family :=
  family.filterMap (sliceClause f name a)

noncomputable def strips (f : Nat → Nat) (name bound : Nat) (family : Family) : List (Nat × Family) :=
  (List.range bound).map (fun a => (a,sliceFamily f name a family))

def coordinates (family : Family) : Finset Nat := supportSet (family.flatMap originalRows)

abbrev dimension (family : Family) : Nat := (coordinates family).card

def ExactOrderedHitExtraction : Prop :=
  ∀ (statuses : List RowResult) (rs : List Row), extractHits statuses = some rs ↔ HitRows statuses rs

def ExactBitClauseSlice : Prop :=
  ∀ (f ρ : Nat → Nat) (name a : Nat) (clause : List BitRow), ρ name = a →
    (ClauseHolds f ρ clause ↔ ∃ child, sliceClause f name a clause = some child ∧ ClauseHolds f ρ child)

def ExactBitClauseProvenance : Prop :=
  ∀ (f : Nat → Nat) (name a : Nat) (clause child : List BitRow), sliceClause f name a clause = some child →
    HitRows (sliceRows f name a (originalRows clause)) (originalRows child) ∧
    wantedBits child = wantedBits clause ∧
    supportSet (originalRows child) = (supportSet (originalRows clause)).erase name

def ExactBitFamilyLowStrips : Prop :=
  ∀ (f ρ : Nat → Nat) (name bound : Nat) (family : Family) (prior : (Nat → Nat) → Prop),
    ((∃ a : Nat, a < bound ∧ let θ := Function.update ρ name a
        prior θ ∧ Holds f θ family) ↔
      ∃ branch ∈ strips f name bound family, let θ := Function.update ρ name branch.1
        prior θ ∧ Holds f θ branch.2)

def ExactBitFamilyLowDimension : Prop :=
  ∀ (f : Nat → Nat) (name bound : Nat) (family : Family), name ∈ coordinates family →
    ∀ branch ∈ strips f name bound family,
      coordinates branch.2 ⊆ (coordinates family).erase name ∧ dimension branch.2 < dimension family

def FullActualBitFamilyLowSlices : Prop :=
  ExactOrderedHitExtraction ∧ ExactBitClauseSlice ∧ ExactBitClauseProvenance ∧
    ExactBitFamilyLowStrips ∧ ExactBitFamilyLowDimension

end LogicLineages.PermittedControl.ActualBitFamilyLowSlices
