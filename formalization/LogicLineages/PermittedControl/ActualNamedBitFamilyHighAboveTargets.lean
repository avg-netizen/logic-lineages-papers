module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family Holds reifyFamily)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualBitFamilyHigh (ranked AllPaid)
open ActualNamedBitFamilyHigh (Supplied Valid charts cutoff)
open ActualFiniteOrderBranches (Pattern)
open ActualRankChartPrototype (readWithin seed)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalRankedLiteralClauseHigh (OriginalSetup highMinimum highPackets)
open ActualSymbolicPredecessorProjection (prepend)
open ActualGreatestRouteResidual (Residual lowerFamily)

/-- A genuinely supplied sufficient cutoff, not an assertion of equality
with the exact named typed cutoff. The high row and emitted lower charts
both use this same supplied number. -/
noncomputable def outputs (C : Nat) (family : Family) (p : Pattern) : List Residual :=
  let qs := (highPackets p.1 (top p) (ranked p family)).map (prepend (top p))
  lowerFamily (top p) C qs

noncomputable def child (C : Nat) (family : Family) (p : Pattern) : Family :=
  reifyFamily C (top p) (outputs C family p)

noncomputable def compile (C : Nat) (family : Family) (names : List Nat) : List (Pattern × Family) :=
  (charts names).map (fun p => (p,child C family p))

def ExactAboveHighSetup : Prop :=
  ∀ (B C : Nat) (family : Family) (names : List Nat), cutoff B family names ≤ C →
    ∀ p : Pattern, Supplied family names → Valid names p →
    ∀ lower : Nat → Nat, LowerChartCondition C (top p) lower →
      OriginalSetup B p.1 (top p) lower (ranked p family) ∧
      ∀ z : Nat, seed C p lower ≤ z → highMinimum B p.1 (top p) lower (ranked p family) ≤ z

def ExactAboveUniformChartChild : Prop :=
  ∀ (f : Nat → Nat) (B C : Nat), SelectedWithThreshold f B →
    ∀ (family : Family) (names : List Nat), Supplied family names → cutoff B family names ≤ C →
    ∀ p : Pattern, Valid names p → ∀ (lower outside : Nat → Nat),
      (Holds f lower (child C family p) ↔
        LowerChartCondition C (top p) lower ∧
        ∃ z : Nat, seed C p lower ≤ z ∧
          AllPaid C family (readWithin names p lower outside z) ∧
          Holds f (readWithin names p lower outside z) family)

def ExactAboveHighExistential : Prop :=
  ∀ (f : Nat → Nat) (B C : Nat), SelectedWithThreshold f B →
    ∀ (family : Family) (names : List Nat), Supplied family names → cutoff B family names ≤ C →
      0 < dimension family →
      ((∃ θ : Nat → Nat, AllPaid C family θ ∧ Holds f θ family) ↔
        ∃ result ∈ compile C family names, ∃ lower : Nat → Nat, Holds f lower result.2)

def ExactAboveHighDimension : Prop :=
  ∀ (C : Nat) (family : Family) (names : List Nat), Supplied family names →
    ∀ result ∈ compile C family names,
      (∀ k ∈ coordinates result.2, k < top result.1) ∧ dimension result.2 < dimension family

def FullActualNamedBitFamilyHighAbove : Prop :=
  ExactAboveHighSetup ∧ ExactAboveUniformChartChild ∧ ExactAboveHighExistential ∧ ExactAboveHighDimension

end LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
