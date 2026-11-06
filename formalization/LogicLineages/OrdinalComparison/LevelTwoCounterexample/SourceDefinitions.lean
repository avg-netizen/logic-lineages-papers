module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarDefinitions
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairDefinitions
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitDefinitions
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceCode
open Source Source.ForwardTranslation

def rawIndex {Γ : List Ty} (c : OrdinalComponent Γ) : Nat :=
  SourceTypedPorts.variableIndex c.2.1

/-- The actual closed positive coordinates, normalized before comparison.
WW strictness is strict only at zero; equality uses both positive directions. -/
def positiveFlag (mode : Nat) (a b : EncodedVector) : Bool :=
  let ab := positiveComparison (a.2.map encodedClosedPositive) (b.2.map encodedClosedPositive)
  if mode = 0 then ab else if mode = 1 then ab else
    ab && positiveComparison (b.2.map encodedClosedPositive) (a.2.map encodedClosedPositive)

noncomputable def sourceRelation {Γ : List Ty} {n m : Nat} (mode : Nat)
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m) (ρ : OrdinalComponent Γ → Nat) : Prop :=
  if mode = 0 then SourceComparisonAt false a b ρ
  else if mode = 1 then SourceComparisonAt true a b ρ
  else ∀ j, sourceVectorAtValue a ρ j = sourceVectorAtValue b ρ j

abbrev Input := Nat × Nat × Nat × Nat

/-- Original term codes enter the actual default canonical assignment and
vector compiler. The existing scalar normalization/adapter and pair graph
compiler are then used literally. No assignment or solver is supplied as an
oracle. Successful output outside the certified level-two class carries no
level-two correctness claim. -/
def compile (p : Input) : Option Pair.Package := do
  let a ← GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.1)
  let b ← GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.2)
  return Pair.Code.package (p.1,p.2.1,positiveFlag p.2.1 a b,
    ScalarCode.lowerSyntax a.1,ScalarCode.lowerSyntax b.1)
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceCode
