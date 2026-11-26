module
public import LogicLineages.PermittedControl.AffineCollapseTopologicalExtensionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseTopologicalLow
open OrdinalComparison
open AffineCollapseTopologicalExtension (Valuation Topological AgreesOutside run)
open AffineCollapsePairListLow (Pair GraphsAt LimitHeads prefixRows prefixSnapshot)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows HitRows)
open HeterogeneousSignedMatrixLowStrips (branches)
open AffineCollapseGuardedLow (OriginalTestAt)

abbrev Prior := Valuation → Valuation → Prop
abbrev Test := Valuation → Snapshot → Prop

def ExactTestedExternalExtension : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (pairs : List Pair), Topological known pairs →
      ∀ (external : Valuation) (prior : Prior) (testRows : List Row) (test : Test) (positive : Bool),
        (∃ final, run f external pairs = some final ∧ prior external final ∧
          ∃ values : Snapshot, actualRows f final testRows values ∧
            OriginalTestAt test positive final values) ↔
        ∃ final, GraphsAt f final pairs ∧ AgreesOutside pairs external final ∧ prior external final ∧
          ∃ values : Snapshot, actualRows f final testRows values ∧
            OriginalTestAt test positive final values

/-- A low coordinate from the original supplied external names is never
produced by a pair. The branch may quantify the produced names, but each
pair and suffix reads the same update, and all other external names are fixed. -/
def ExactTopologicalExternalLow : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (pairs : List Pair), Topological known pairs → LimitHeads pairs →
      ∀ (base : Valuation) (rank bound : Nat), rank ∈ known →
        ∀ (prior : Prior) (testRows : List Row) (test : Test) (positive : Bool),
          (∃ a : Nat, a < bound ∧
            let external := Function.update base rank a
            ∃ final, run f external pairs = some final ∧ prior external final ∧
              ∃ values : Snapshot, actualRows f final testRows values ∧
                OriginalTestAt test positive final values) ↔
          ∃ branch residual,
            branch ∈ branches f rank bound (prefixRows pairs ++ testRows) ∧ HitRows branch.2 residual ∧
            ∃ sharedBase : Valuation, AgreesOutside pairs base sharedBase ∧
              let external := Function.update base rank branch.1
              let final := Function.update sharedBase rank branch.1
              prior external final ∧ ∃ values : Snapshot,
                actualRows f final residual (prefixSnapshot final pairs ++ values) ∧
                  OriginalTestAt test positive final values

def FullAffineCollapseTopologicalLow : Prop :=
  ExactTestedExternalExtension ∧ ExactTopologicalExternalLow

end LogicLineages.PermittedControl.AffineCollapseTopologicalLow
