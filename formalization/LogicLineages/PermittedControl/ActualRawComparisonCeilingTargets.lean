module
public import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingTargets
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawComparisonCeiling
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open ActualFullValueLabels (Label operandLabel)
open ActualFullLabelPairGuards (Pair cost)
open ActualGlobalComparisonCeiling (comparisonCeiling onAlphabet)
open ActualSyntaxChargeBudget (syntaxBudgetCode)
open ActualZeroEdgeAlphabetCode (AlphabetCode collectCode)

abbrev LabelCode := Nat × LongFieldCode
abbrev PairCode := LabelCode × LabelCode

def encodeLabel (l : Label) : LabelCode := (l.rank,longFieldCode l.field)
def encodePair (p : Pair) : PairCode := (encodeLabel p.1,encodeLabel p.2)

def labelCode (op : LowerOperandCode) : Option LabelCode :=
  if op.1 = 1 then
    if op.2.2.1 = 0 ∧ op.2.2.2.1 = 0 then none else some (op.2.1,op.2.2)
  else if op.1 = 2 then
    (ActualCountCoreLabels.rawLabel op.2.2.2.2.1 op.2.2.2.2.2).map (Prod.mk op.2.1)
  else none

def fieldNormCode (field : LongFieldCode) : Nat :=
  if field.1 = 0 then 0 else rawNormCode field.2.2.1

def orientedMinimumCode (B : Nat) (p q : LongFieldCode) : Nat :=
  max (highFieldComparisonBoundCode B p q) (max (fieldNormCode p) (fieldNormCode q))

def pairCostCode (B : Nat) (pair : PairCode) : Nat :=
  max (orientedMinimumCode B pair.1.2 pair.2.2) (orientedMinimumCode B pair.2.2 pair.1.2)

def orderedPairs (ls : List LabelCode) : List PairCode :=
  ls.flatMap (fun l => ls.map (fun r => (l,r)))

def alphabetCode (B : Nat) (ops : AlphabetCode) : Nat :=
  (orderedPairs (ops.filterMap labelCode)).foldr (fun p n => max (pairCostCode B p) n) 0

def cutoffCode (B r : Nat) (terms : List WeightedCode) : Nat :=
  alphabetCode B (collectCode (syntaxBudgetCode r terms) (terms.map Prod.snd))

def ExactRawComparisonCeilingCalibration : Prop :=
  (∀ op : LowerOperand, labelCode op.code = (operandLabel op).map encodeLabel) ∧
  (∀ (B : Nat) (p : Pair), pairCostCode B (encodePair p) = cost B p) ∧
  (∀ (B : Nat) (ops : List LowerOperand), alphabetCode B (ops.map LowerOperand.code) = onAlphabet B ops) ∧
  ∀ (B r : Nat) (terms : List WeightedOperand),
    cutoffCode B r (terms.map encodeWeighted) = comparisonCeiling B r terms

def ExactRawComparisonCeilingEffectivity : Prop :=
  Primrec labelCode ∧ Primrec₂ pairCostCode ∧ Primrec₂ alphabetCode ∧
  Primrec (fun p : Nat × Nat × List WeightedCode => cutoffCode p.1 p.2.1 p.2.2)

def FullActualRawComparisonCeiling : Prop :=
  ExactRawComparisonCeilingCalibration ∧ ExactRawComparisonCeilingEffectivity

end LogicLineages.PermittedControl.ActualRawComparisonCeiling
