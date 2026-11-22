module
public import LogicLineages.PermittedControl.ActualRawStageCutoffTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawChartsPrimitiveProof
import LogicLineages.PermittedControl.ActualBitFamilyRawRankPrimitiveProof
import LogicLineages.PermittedControl.ActualRawMixedFamilyCeilingPrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawStageCutoff
open ActualBitFamilyRawLayout (RawFamily)
open ActualBitFamilyRawCharts (charts exactRawChartEffectivity)
open ActualFiniteOrderBranches (Pattern)
open ActualRawMixedFamilyCeiling (familyBoundPrimitive)

theorem chartCostPrimitive :
    Primrec (fun p : Nat × RawFamily × Pattern => chartCost p.1 p.2.1 p.2.2) := by
  let A := Nat × RawFamily × Pattern
  have B : Primrec (Prod.fst : A → Nat) := Primrec.fst
  have raw : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have chart : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have width : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp chart
  have ranked := ActualBitFamilyRawRank.familyPrimitive.comp (chart.pair raw)
  exact (familyBoundPrimitive.comp (B.pair (width.pair ranked))).of_eq (fun _ => rfl)

private theorem foldMaximum {A X : Type} [Primcodable A] [Primcodable X]
    {items : A → List X} {cost : A → X → Nat} (hi : Primrec items) (hc : Primrec₂ cost) :
    Primrec (fun a => (items a).foldr (fun p n => max (cost a p) n) 0) := by
  let S := A × (X × Nat)
  have root : Primrec (Prod.fst : S → A) := Primrec.fst
  have p : Primrec (fun s : S => s.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun s : S => s.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun s : S => max (cost s.1 s.2.1) s.2.2) :=
    Primrec.nat_max.comp (hc.comp root p) n
  exact Primrec.list_foldr hi (Primrec.const 0) step.to₂

private def chartArgs (p : (Nat × RawFamily) × Pattern) : Nat × RawFamily × Pattern :=
  (p.1.1,p.1.2,p.2)

private theorem chartArgsPrimitive : Primrec chartArgs := by
  let A := (Nat × RawFamily) × Pattern
  have B : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have raw : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  exact B.pair (raw.pair Primrec.snd)

private theorem chartArgsLiteral (p : (Nat × RawFamily) × Pattern) :
    chartCost (chartArgs p).1 (chartArgs p).2.1 (chartArgs p).2.2 =
      chartCost p.1.1 p.1.2 p.2 := rfl

private theorem chartCostLifted :
    Primrec (fun p : (Nat × RawFamily) × Pattern => chartCost p.1.1 p.1.2 p.2) :=
  (chartCostPrimitive.comp chartArgsPrimitive).of_eq chartArgsLiteral

private theorem chartCostCurried :
    Primrec₂ (fun (p : Nat × RawFamily) (chart : Pattern) => chartCost p.1 p.2 chart) :=
  chartCostLifted.to₂

private theorem stageLiteral (p : Nat × RawFamily) :
    (charts p.2).foldr (fun c n => max (chartCost p.1 p.2 c) n) 0 = stageBound p.1 p.2 := rfl

private theorem stageBoundUncurried :
    Primrec (fun p : Nat × RawFamily => stageBound p.1 p.2) := by
  have tape : Primrec (fun p : Nat × RawFamily => charts p.2) :=
    exactRawChartEffectivity.2.2.2.2.comp Primrec.snd
  exact (foldMaximum tape chartCostCurried).of_eq stageLiteral

theorem stageBoundPrimitive : Primrec₂ stageBound := stageBoundUncurried.to₂

theorem exactRawStageCutoffEffectivity : ExactRawStageCutoffEffectivity :=
  ⟨chartCostPrimitive,stageBoundPrimitive⟩

end LogicLineages.PermittedControl.ActualRawStageCutoff
