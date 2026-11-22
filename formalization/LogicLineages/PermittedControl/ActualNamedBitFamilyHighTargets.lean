module
public import LogicLineages.PermittedControl.ActualBitFamilyHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyHigh
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family Holds reifyFamily)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualBitFamilyHigh (ranked AllPaid)
open ActualFiniteOrderBranches (Pattern patterns rename)
open ActualRankChartPrototype (Consistent readWithin seed)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalRankedLiteralClauseHigh (familyNeed OriginalSetup highMinimum highPackets)
open ActualSymbolicPredecessorProjection (prepend)
open ActualGreatestRouteResidual (Residual lowerFamily)

def Supplied (family : Family) (names : List Nat) : Prop :=
  names.Nodup ∧ ∀ k : Nat, k ∈ names ↔ k ∈ coordinates family

def Valid (names : List Nat) (p : Pattern) : Prop :=
  p ∈ patterns names ∧ 0 < p.1 ∧ Consistent p

noncomputable def charts (names : List Nat) : List Pattern :=
  (patterns names).filter (fun p => @decide (0 < p.1 ∧ Consistent p) (Classical.propDecidable _))

noncomputable def cutoff (B : Nat) (family : Family) (names : List Nat) : Nat :=
  (charts names).foldr (fun p n => max (familyNeed B p.1 (ranked p family)) n) 0

noncomputable def outputs (B : Nat) (family : Family) (names : List Nat) (p : Pattern) : List Residual :=
  let qs := (highPackets p.1 (top p) (ranked p family)).map (prepend (top p))
  lowerFamily (top p) (cutoff B family names) qs

noncomputable def child (B : Nat) (family : Family) (names : List Nat) (p : Pattern) : Family :=
  reifyFamily (cutoff B family names) (top p) (outputs B family names p)

noncomputable def compile (B : Nat) (family : Family) (names : List Nat) : List (Pattern × Family) :=
  (charts names).map (fun p => (p,child B family names p))

def ExactNamedCharts : Prop :=
  ∀ (names : List Nat) (p : Pattern), p ∈ charts names ↔ Valid names p

def ExactNamedHighSetup : Prop :=
  ∀ (B : Nat) (family : Family) (names : List Nat) (p : Pattern),
    Supplied family names → Valid names p →
    ∀ lower : Nat → Nat, LowerChartCondition (cutoff B family names) (top p) lower →
      OriginalSetup B p.1 (top p) lower (ranked p family) ∧
      ∀ z : Nat, seed (cutoff B family names) p lower ≤ z →
        highMinimum B p.1 (top p) lower (ranked p family) ≤ z

def ExactNamedUniformChartChild : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (family : Family) (names : List Nat) (p : Pattern), Supplied family names → Valid names p →
      ∀ (lower outside : Nat → Nat),
        (Holds f lower (child B family names p) ↔
          LowerChartCondition (cutoff B family names) (top p) lower ∧
          ∃ z : Nat, seed (cutoff B family names) p lower ≤ z ∧
            AllPaid (cutoff B family names) family (readWithin names p lower outside z) ∧
            Holds f (readWithin names p lower outside z) family)

def ExactNamedHighExistential : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (family : Family) (names : List Nat), Supplied family names → 0 < dimension family →
      ((∃ θ : Nat → Nat, AllPaid (cutoff B family names) family θ ∧ Holds f θ family) ↔
        ∃ result ∈ compile B family names, ∃ lower : Nat → Nat, Holds f lower result.2)

def ExactNamedHighDimension : Prop :=
  ∀ (B : Nat) (family : Family) (names : List Nat), Supplied family names →
    ∀ result ∈ compile B family names,
      (∀ k ∈ coordinates result.2, k < top result.1) ∧ dimension result.2 < dimension family

def FullActualNamedBitFamilyHigh : Prop :=
  ExactNamedCharts ∧ ExactNamedHighSetup ∧ ExactNamedUniformChartChild ∧
    ExactNamedHighExistential ∧ ExactNamedHighDimension

end LogicLineages.PermittedControl.ActualNamedBitFamilyHigh
