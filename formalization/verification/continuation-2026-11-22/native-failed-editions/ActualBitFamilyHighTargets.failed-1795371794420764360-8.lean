module
public import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesTargets
public import LogicLineages.PermittedControl.ActualRankChartPrototypeTargets
public import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyHigh
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family Holds reifyFamily)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualFiniteOrderBranches (Pattern patterns rename)
open ActualRankChartPrototype (Consistent readWithin seed)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedTerminalBitClauses (BitRow)
open OriginalMatrixDenseRanks (renameRow)
open OriginalRankedLiteralClauseHigh (familyNeed OriginalSetup highMinimum highPackets)
open ActualSymbolicPredecessorProjection (prepend)
open ActualGreatestRouteResidual (Residual lowerFamily)

def names (family : Family) : List Nat := (coordinates family).toList

def renameBit (p : Pattern) (row : BitRow) : BitRow := (renameRow (rename p) row.1,row.2)

def ranked (p : Pattern) (family : Family) : Family := family.map (List.map (renameBit p))

def ValidChart (family : Family) (p : Pattern) : Prop :=
  p ∈ patterns (names family) ∧ 0 < p.1 ∧ Consistent p

noncomputable def charts (family : Family) : List Pattern :=
  (patterns (names family)).filter
    (fun p => @decide (0 < p.1 ∧ Consistent p) (Classical.propDecidable _))

/-- Static cutoff over the actual finite ranked families, independent of
all numerical valuations and of the eventual chosen chart. -/
noncomputable def cutoff (B : Nat) (family : Family) : Nat :=
  (charts family).foldr (fun p n => max (familyNeed B p.1 (ranked p family)) n) 0

def AllPaid (C : Nat) (family : Family) (ρ : Nat → Nat) : Prop :=
  ∀ k ∈ coordinates family, C ≤ ρ k

noncomputable def outputs (B : Nat) (family : Family) (p : Pattern) : List Residual :=
  let qs := (highPackets p.1 (top p) (ranked p family)).map (prepend (top p))
  lowerFamily (top p) (cutoff B family) qs

noncomputable def child (B : Nat) (family : Family) (p : Pattern) : Family :=
  reifyFamily (cutoff B family) (top p) (outputs B family p)

noncomputable def compile (B : Nat) (family : Family) : List (Pattern × Family) :=
  (charts family).map (fun p => (p,child B family p))

def ExactValidGenericCharts : Prop :=
  ∀ (family : Family) (p : Pattern), p ∈ charts family ↔ ValidChart family p

def ExactGenericRankTransport : Prop :=
  ∀ (f θ σ : Nat → Nat) (family : Family) (p : Pattern),
    (∀ k ∈ coordinates family, σ (rename p k) = θ k) →
      (Holds f θ family ↔ Holds f σ (ranked p family))

def ExactGenericHighSetup : Prop :=
  ∀ (B : Nat) (family : Family) (p : Pattern), ValidChart family p →
    ∀ lower : Nat → Nat, LowerChartCondition (cutoff B family) (top p) lower →
      OriginalSetup B p.1 (top p) lower (ranked p family) ∧
      ∀ z : Nat, seed (cutoff B family) p lower ≤ z →
        highMinimum B p.1 (top p) lower (ranked p family) ≤ z

def ExactGenericUniformChartChild : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (family : Family) (p : Pattern), ValidChart family p →
      ∀ (lower outside : Nat → Nat),
        (Holds f lower (child B family p) ↔
          LowerChartCondition (cutoff B family) (top p) lower ∧
          ∃ z : Nat, seed (cutoff B family) p lower ≤ z ∧
            AllPaid (cutoff B family) family (readWithin (names family) p lower outside z) ∧
            Holds f (readWithin (names family) p lower outside z) family)

def ExactGenericHighExistential : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ family : Family, 0 < dimension family →
      ((∃ θ : Nat → Nat, AllPaid (cutoff B family) family θ ∧ Holds f θ family) ↔
        ∃ result ∈ compile B family, ∃ lower : Nat → Nat, Holds f lower result.2)

def ExactGenericHighDimension : Prop :=
  ∀ (B : Nat) (family : Family), ∀ result ∈ compile B family,
    (∀ k ∈ coordinates result.2, k < top result.1) ∧ dimension result.2 < dimension family

def FullActualBitFamilyHigh : Prop :=
  ExactValidGenericCharts ∧ ExactGenericRankTransport ∧ ExactGenericHighSetup ∧
    ExactGenericUniformChartChild ∧ ExactGenericHighExistential ∧ ExactGenericHighDimension

end LogicLineages.PermittedControl.ActualBitFamilyHigh
