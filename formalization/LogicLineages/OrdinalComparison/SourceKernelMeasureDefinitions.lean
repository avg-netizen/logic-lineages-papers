module
public import LogicLineages.OrdinalComparison.ComparisonSignatureDefinitions
public import LogicLineages.OrdinalComparison.ComparisonMeasureDefinitions
public import Mathlib.Data.List.Perm.Basic

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Actual source principal exponents, retaining every occurrence. Literal
masses are ignored ONLY by the termination measure. -/
structure ComparisonSourceMeasureState where
  heads : Nat
  exponents : List NONote

def comparisonSourceKernelRanks (budget : Nat) (w : List NONote) : List Nat :=
  w.map (fun eta => encodedComparisonSignatureRank budget (rawNoteEncode eta.1))

/-- Source reverse-weight kernel transformation on ACTUAL normal ordinals:
remove one bounded principal and add any finite collection of strictly
higher bounded principals, preserving all other occurrences up to ordering.
The actual source call graph has not been supplied by this definition. -/
def ComparisonSourceKernelStep (budget : Nat)
    (next current : ComparisonSourceMeasureState) : Prop :=
  next.heads<current.heads ∨
    (next.heads=current.heads ∧ ∃ (before after added : List NONote) (eta : NONote),
      Vendor.R1.treeWeight eta.1≤budget ∧
      (∀ sigma∈added,Vendor.R1.treeWeight sigma.1≤budget ∧ eta.1.repr<sigma.1.repr) ∧
      current.exponents.Perm (before++eta::after) ∧ next.exponents.Perm (before++added++after))

end LogicLineages.OrdinalComparison
