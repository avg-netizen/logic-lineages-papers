module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets
public import LogicLineages.PermittedControl.ActualRankChartPrototypeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawCharts
open ActualBitFamilyRawLayout (RawFamily names encodeFamily)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualFiniteOrderBranches (Entry Pattern Dense choices onto patterns guard rename realized)
open ActualRankChartPrototype (Consistent)

def nonemptyPatterns (source : List Nat) : List Pattern :=
  (patterns source).filter (fun p => decide (0 < p.1))

def charts (raw : RawFamily) : List Pattern := nonemptyPatterns (names raw)

def ExactNonemptyPatterns : Prop :=
  ∀ (source : List Nat), source.Nodup → ∀ p : Pattern,
    p ∈ nonemptyPatterns source ↔ Dense source p ∧ 0 < p.1 ∧ Consistent p

def ExactRawChartEnumeration : Prop :=
  ∀ (raw : RawFamily) (p : Pattern),
    p ∈ charts raw ↔ Dense (names raw) p ∧ 0 < p.1 ∧ Consistent p

/-- Every valuation on the original coordinates induces a true emitted
chart. The conclusions are about actual values, not ordering equality of
different coordinate-list representations. -/
def ExactEncodedRawChartCoverage : Prop :=
  ∀ (family : Family), 0 < dimension family → ∀ θ : Nat → Nat,
    ∃ p ∈ charts (encodeFamily family),
      (guard p).eval θ ∧ p.1 ≤ dimension family ∧ StrictMono (realized θ p) ∧
      ∀ k ∈ coordinates family, rename p k < p.1 ∧ realized θ p (rename p k) = θ k

def ExactRawChartEffectivity : Prop :=
  Primrec (fun p : Nat × List Nat => choices p.1 p.2) ∧
  Primrec (fun p : Nat × List Entry => onto p.1 p.2) ∧ Primrec patterns ∧
  Primrec nonemptyPatterns ∧ Primrec charts

def FullActualBitFamilyRawCharts : Prop :=
  ExactNonemptyPatterns ∧ ExactRawChartEnumeration ∧ ExactEncodedRawChartCoverage ∧
    ExactRawChartEffectivity

end LogicLineages.PermittedControl.ActualBitFamilyRawCharts
