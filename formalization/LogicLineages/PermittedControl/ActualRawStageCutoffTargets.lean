module
public import LogicLineages.PermittedControl.ActualBitFamilyRawChartsTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawRankTargets
public import LogicLineages.PermittedControl.ActualRawMixedFamilyCeilingTargets
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawStageCutoff
open ActualBitFamilyRawLayout (RawFamily names encodeFamily)
open ActualGuardedResidualBitFamily (Family)
open ActualFiniteOrderBranches (Pattern)
open ActualNamedBitFamilyHigh (Supplied cutoff)
open ActualBitFamilyHigh (ranked)
open OriginalRankedLiteralClauseHigh (familyNeed)
open ActualRawMixedFamilyCeiling (familyBound)

def chartCost (B : Nat) (raw : RawFamily) (p : Pattern) : Nat :=
  familyBound B p.1 (ActualBitFamilyRawRank.familyCode (p,raw))

def stageBound (B : Nat) (raw : RawFamily) : Nat :=
  (ActualBitFamilyRawCharts.charts raw).foldr (fun p n => max (chartCost B raw p) n) 0

def ExactRawStageNamesAndCharts : Prop :=
  (∀ source : List Nat, source.Nodup →
    ActualBitFamilyRawCharts.nonemptyPatterns source = ActualNamedBitFamilyHigh.charts source) ∧
  ∀ family : Family,
    let source := names (encodeFamily family)
    Supplied family source ∧
    ActualBitFamilyRawCharts.charts (encodeFamily family) = ActualNamedBitFamilyHigh.charts source

def ExactRawRankedChartCost : Prop :=
  (∀ (B : Nat) (family : Family) (p : Pattern),
    familyNeed B p.1 (ranked p family) ≤ chartCost B (encodeFamily family) p) ∧
  ∀ (B : Nat) (family : Family) (p : Pattern),
    p ∈ ActualNamedBitFamilyHigh.charts (names (encodeFamily family)) →
      familyNeed B p.1 (ranked p family) ≤ stageBound B (encodeFamily family)

def ExactRawStageCutoffMajorant : Prop :=
  ∀ (B : Nat) (family : Family),
    cutoff B family (names (encodeFamily family)) ≤ stageBound B (encodeFamily family)

def ExactRawStageCutoffEffectivity : Prop :=
  Primrec (fun p : Nat × RawFamily × Pattern => chartCost p.1 p.2.1 p.2.2) ∧ Primrec₂ stageBound

def FullActualRawStageCutoff : Prop :=
  ExactRawStageNamesAndCharts ∧ ExactRawRankedChartCost ∧ ExactRawStageCutoffMajorant ∧
    ExactRawStageCutoffEffectivity

end LogicLineages.PermittedControl.ActualRawStageCutoff
