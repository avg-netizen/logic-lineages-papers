module
public import LogicLineages.PermittedControl.ActualRawComparisonCeilingTargets
import LogicLineages.PermittedControl.ActualRawComparisonCeilingLabelPrimitiveProof
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodePrimitiveProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import LogicLineages.PermittedControl.HighFieldComparisonPrimitiveProof
import LogicLineages.OrdinalComparison.RawNormCode
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawComparisonCeiling
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedCode)
open ActualZeroEdgeAlphabetCode (AlphabetCode collectCode codeEffectivity)
open ActualSyntaxChargeBudget (syntaxBudgetCode budgetCodeExact)

private theorem fieldNormPrimitive : Primrec fieldNormCode := by
  have status : Primrec (fun field : LongFieldCode => field.1) := Primrec.fst
  have upper : Primrec (fun field : LongFieldCode => field.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have code : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  exact Primrec.ite (Primrec.eq.comp status (Primrec.const 0)) (Primrec.const 0) (code.comp upper)

private theorem orientedMinimumPrimitive :
    Primrec (fun args : Nat × LongFieldCode × LongFieldCode =>
      orientedMinimumCode args.1 args.2.1 args.2.2) := by
  let A := Nat × LongFieldCode × LongFieldCode
  have left : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have right : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.nat_max.comp highFieldComparisonEffective.2.2.1
    (Primrec.nat_max.comp (fieldNormPrimitive.comp left) (fieldNormPrimitive.comp right))

/-- Keep the two field projections and their cost arguments abstract while
assembling the primitive recursion proof. This avoids unfolding the
ordinal comparison program while inferring the product codecs. -/
private theorem liftedPairCosts {F L : Type} [Primcodable F] [Primcodable L]
    {field : L → F} {oriented : Nat → F → F → Nat}
    (key : Primrec field)
    (cost : Primrec (fun p : Nat × F × F => oriented p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Nat × (L × L) =>
      max (oriented p.1 (field p.2.1) (field p.2.2))
        (oriented p.1 (field p.2.2) (field p.2.1))) := by
  let A := Nat × (L × L)
  have B : Primrec (fun p : A => p.1) := Primrec.fst
  have x : Primrec (fun p : A => field p.2.1) := key.comp (Primrec.fst.comp Primrec.snd)
  have y : Primrec (fun p : A => field p.2.2) := key.comp (Primrec.snd.comp Primrec.snd)
  have forward : Primrec (fun p : A => oriented p.1 (field p.2.1) (field p.2.2)) :=
    cost.comp (B.pair (x.pair y))
  have backward : Primrec (fun p : A => oriented p.1 (field p.2.2) (field p.2.1)) :=
    cost.comp (B.pair (y.pair x))
  exact Primrec.nat_max.comp forward backward

private theorem pairCostUncurried :
    Primrec (fun p : Nat × PairCode => pairCostCode p.1 p.2) := by
  have asFields :=
    liftedPairCosts (Primrec.snd : Primrec (Prod.snd : LabelCode → LongFieldCode))
      orientedMinimumPrimitive
  exact asFields.of_eq (fun _ => rfl)

theorem pairCostPrimitive : Primrec₂ pairCostCode := pairCostUncurried.to₂

private theorem orderedPairsPrimitive : Primrec orderedPairs := by
  let A := List LabelCode × LabelCode
  let R := A × LabelCode
  have left : Primrec (fun p : R => p.1.2) := Primrec.snd.comp Primrec.fst
  have right : Primrec (fun p : R => p.2) := Primrec.snd
  have one : Primrec (fun p : A => p.1.map (Prod.mk p.2)) :=
    Primrec.list_map Primrec.fst (left.pair right).to₂
  exact Primrec.list_flatMap Primrec.id one.to₂

private theorem foldMaximumWith {A X : Type} [Primcodable A] [Primcodable X]
    {xs : A → List X} {cost : A → X → Nat} (items : Primrec xs) (eval : Primrec₂ cost) :
    Primrec (fun a => (xs a).foldr (fun x n => max (cost a x) n) 0) := by
  let Q := A × (X × Nat)
  have cfg : Primrec (Prod.fst : Q → A) := Primrec.fst
  have item : Primrec (fun p : Q => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : Q => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : Q => max (cost p.1 p.2.1) p.2.2) :=
    Primrec.nat_max.comp (eval.comp cfg item) acc
  exact Primrec.list_foldr items (Primrec.const 0) step.to₂

private theorem pairTapePrimitive :
    Primrec (fun xs : AlphabetCode => orderedPairs (xs.filterMap labelCode)) := by
  have labelTape : Primrec (fun xs : AlphabetCode => xs.filterMap labelCode) :=
    Primrec.listFilterMap Primrec.id (labelPrimitive.comp Primrec.snd).to₂
  exact orderedPairsPrimitive.comp labelTape

private theorem foldMaximumWithConfig {A X C : Type}
    [Primcodable A] [Primcodable X] [Primcodable C]
    {xs : A → List X} {cfg : A → C} {cost : C → X → Nat}
    (items : Primrec xs) (config : Primrec cfg) (eval : Primrec₂ cost) :
    Primrec (fun a => (xs a).foldr (fun x n => max (cost (cfg a) x) n) 0) :=
  foldMaximumWith items (eval.comp₂ (config.comp₂ Primrec₂.left) Primrec₂.right)

private theorem alphabetFoldLiteral (p : Nat × AlphabetCode) :
    (orderedPairs (p.2.filterMap labelCode)).foldr
      (fun x n => max (pairCostCode p.1 x) n) 0 = alphabetCode p.1 p.2 :=
  rfl

private theorem alphabetUncurried :
    Primrec (fun p : Nat × AlphabetCode => alphabetCode p.1 p.2) := by
  let A := Nat × AlphabetCode
  have tape : Primrec (fun p : A => orderedPairs (p.2.filterMap labelCode)) :=
    pairTapePrimitive.comp (Primrec.snd : Primrec (Prod.snd : A → AlphabetCode))
  have cfg : Primrec (Prod.fst : A → Nat) := Primrec.fst
  have folded : Primrec (fun p : A => (orderedPairs (p.2.filterMap labelCode)).foldr
      (fun x n => max (pairCostCode p.1 x) n) 0) :=
    foldMaximumWithConfig tape cfg pairCostPrimitive
  exact folded.of_eq alphabetFoldLiteral

theorem alphabetPrimitive : Primrec₂ alphabetCode := alphabetUncurried.to₂

theorem budgetPrimitive :
    Primrec (fun p : Nat × Nat × List WeightedCode => cutoffCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × List WeightedCode
  have B : Primrec (fun p : A => p.1) := Primrec.fst
  have r : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have terms : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have ops : Primrec (fun p : A => p.2.2.map Prod.snd) :=
    Primrec.list_map terms
      ((Primrec.snd : Primrec (Prod.snd : WeightedCode → LowerOperandCode)).comp Primrec.snd).to₂
  have budget := budgetCodeExact.1.comp r terms
  exact alphabetPrimitive.comp B (codeEffectivity.2.2.comp budget ops)

theorem exactRawComparisonCeilingEffectivity : ExactRawComparisonCeilingEffectivity :=
  ⟨labelPrimitive,pairCostPrimitive,alphabetPrimitive,budgetPrimitive⟩

end LogicLineages.PermittedControl.ActualRawComparisonCeiling
