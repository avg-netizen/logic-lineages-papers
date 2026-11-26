module
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowLowStrips
open OrdinalComparison PreparedProjection SignedRowCoordinateSlice
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)

abbrev FamilyArgs := Nat × Nat × Int × List WeightedCode

noncomputable def branchesCode (f : Nat → Nat) (args : FamilyArgs) :
    List (Nat × Result LowerOperandCode) :=
  let (rank,bound,c,terms) := args
  (List.range bound).map (fun a => (a,sliceCode f (rank,a,c,terms)))

noncomputable def branches (f : Nat → Nat) (rank bound : Nat) (c : Int)
    (terms : List WeightedOperand) : List (Nat × Result LowerOperand) :=
  (List.range bound).map (fun a => (a,slice f rank a c terms))

def encodeBranch (p : Nat × Result LowerOperand) : Nat × Result LowerOperandCode :=
  (p.1,p.2.map (Option.map encodeResidual))

/-- Every raw value below the bound is present in order with its original
invalid, miss, or hit status. Canonical slices calibrate literally. -/
def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (branchesCode f)) ∧
  (∀ (f : Nat → Nat) (args : FamilyArgs), (branchesCode f args).map Prod.fst = List.range args.2.1) ∧
  ∀ (f : Nat → Nat) (rank bound : Nat) (c : Int) (terms : List WeightedOperand),
    branchesCode f (rank,bound,c,terms.map encodeWeighted) =
      (branches f rank bound c terms).map encodeBranch

/-- The inherited guard is evaluated at the same raw valuation on both
sides. Other raw coordinates are arbitrary, including below the cutoff. -/
def GuardedLowRow : Prop :=
  ∀ (f ρ : Nat → Nat) (prior : (Nat → Nat) → Prop)
      (rank bound m : Nat) (c : Int) (terms : List WeightedOperand),
    0 < m →
      (∃ a : Nat, a < bound ∧
        prior (Function.update ρ rank a) ∧ denotes f (Function.update ρ rank a) m c terms) ↔
      (∃ (a : Nat) (b : Int) (rest : List WeightedOperand),
        (a,some (some (b,rest))) ∈ branches f rank bound c terms ∧
        prior (Function.update ρ rank a) ∧ denotes f (Function.update ρ rank a) m b rest)

def FullSignedRowLowStrips : Prop := CodeExact ∧ GuardedLowRow

end LogicLineages.PermittedControl.SignedRowLowStrips
