module
public import LogicLineages.PermittedControl.ActualRawComparisonCeilingTargets
import LogicLineages.PermittedControl.ActualRawComparisonCeilingLabelPrimitiveProof
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodePrimitiveProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import LogicLineages.PermittedControl.HighFieldComparisonPrimitiveProof
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

theorem pairCostPrimitive : Primrec₂ pairCostCode := by
  let A := Nat × PairCode
  have B : Primrec (fun p : A => p.1) := Primrec.fst
  have x : Primrec (fun p : A => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have y : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have both : Primrec (fun p : A => pairCostCode p.1 p.2) :=
    Primrec.nat_max.comp (orientedMinimumPrimitive.comp (B.pair (x.pair y)))
      (orientedMinimumPrimitive.comp (B.pair (y.pair x)))
  exact both.to₂

private theorem orderedPairsPrimitive : Primrec orderedPairs := by
  let A := List LabelCode × LabelCode
  let R := A × LabelCode
  have left : Primrec (fun p : R => p.1.2) := Primrec.snd.comp Primrec.fst
  have right : Primrec (fun p : R => p.2) := Primrec.snd
  have one : Primrec (fun p : A => p.1.map (Prod.mk p.2)) :=
    Primrec.list_map Primrec.fst (left.pair right).to₂
  exact Primrec.list_flatMap Primrec.id one.to₂

theorem alphabetPrimitive : Primrec₂ alphabetCode := by
  let A := Nat × AlphabetCode
  let Q := A × (PairCode × Nat)
  have labelTape : Primrec (fun xs : AlphabetCode => xs.filterMap labelCode) :=
    Primrec.listFilterMap Primrec.id (labelPrimitive.comp Primrec.snd).to₂
  have pairTape : Primrec (fun p : A => orderedPairs (p.2.filterMap labelCode)) :=
    orderedPairsPrimitive.comp (labelTape.comp Primrec.snd)
  have cfg : Primrec (fun p : Q => p.1.1) := Primrec.fst.comp Primrec.fst
  have item : Primrec (fun p : Q => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : Q => p.2.2) := Primrec.snd.comp Primrec.snd
  have all : Primrec (fun p : A => alphabetCode p.1 p.2) :=
    Primrec.list_foldr pairTape (Primrec.const 0)
      (Primrec.nat_max.comp (pairCostPrimitive.comp cfg item) acc).to₂
  exact all.to₂

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
