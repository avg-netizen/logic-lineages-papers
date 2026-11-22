module
public import LogicLineages.PermittedControl.ActualRawComparisonCeilingTargets
import LogicLineages.PermittedControl.ActualCountCoreLabelsSyntaxProof
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeCalibrationProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawComparisonCeiling
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualFullValueLabels (Label operandLabel)
open ActualFullLabelPairGuards (Pair cost)
open ActualFiniteFullValueGuards (familyCost pairs)
open ActualGlobalComparisonCeiling (onAlphabet alphabetLabels comparisonCeiling budgetAlphabet)
open ActualSyntaxChargeBudget (syntaxBudgetCode syntaxBudget budgetCodeExact)
open ActualZeroEdgeAlphabetCode (collectCode codeCalibration)
open ActualCountCoreLabels (rawLabel fieldLabel exactCountCoreClassifier)

theorem labelCalibration (op : LowerOperand) :
    labelCode op.code = (operandLabel op).map encodeLabel := by
  cases op with
  | coordinate k => rfl
  | ordinary k f =>
      cases f with
      | iterate a => cases a <;> rfl
      | entry a lam mu => rfl
  | count k lam mu =>
    have calibration := (exactCountCoreClassifier lam mu).2.2.2.2.2
    change (rawLabel (rawNoteEncode lam.1) (rawNoteEncode mu.1)).map (Prod.mk k) =
      ((fieldLabel lam mu).map (fun f => (⟨k,f⟩ : Label))).map encodeLabel
    rw [calibration]
    cases fieldLabel lam mu <;> rfl

private theorem normCalibration (f : ValueField) :
    fieldNormCode (longFieldCode f) = ActualSignedOrdinaryPairHigh.normCode f := by
  cases f <;> rfl

private theorem minimumCalibration (B : Nat) (f g : ValueField) :
    orientedMinimumCode B (longFieldCode f) (longFieldCode g) =
      ActualSignedOrdinaryPairHigh.minimum B f g := by
  simp only [orientedMinimumCode,ActualSignedOrdinaryPairHigh.minimum,normCalibration]

theorem pairCalibration (B : Nat) (p : Pair) :
    pairCostCode B (encodePair p) = cost B p := by
  simp only [pairCostCode,encodePair,encodeLabel,cost,minimumCalibration]

private theorem labelsCalibration (ops : List LowerOperand) :
    (ops.map LowerOperand.code).filterMap labelCode = (alphabetLabels ops).map encodeLabel := by
  induction ops with
  | nil => rfl
  | cons head tail ih =>
      simp only [alphabetLabels,List.map_cons,List.filterMap_cons,labelCalibration]
      cases h : operandLabel head with
      | none =>
          simp only [h,Option.map_none]
          change (tail.map LowerOperand.code).filterMap labelCode =
            (alphabetLabels tail).map encodeLabel
          exact ih
      | some label =>
          simp only [h,Option.map_some]
          change encodeLabel label :: (tail.map LowerOperand.code).filterMap labelCode =
            encodeLabel label :: (alphabetLabels tail).map encodeLabel
          exact congrArg (List.cons (encodeLabel label)) ih

private theorem pairTapeCalibration (ls : List Label) :
    orderedPairs (ls.map encodeLabel) = (pairs ls).map encodePair := by
  unfold orderedPairs pairs
  rw [List.flatMap_map,List.map_flatMap]
  apply congrArg (fun g : Label → List PairCode => ls.flatMap g)
  funext l
  simp only [List.map_map,Function.comp_def,encodePair]

private theorem foldCalibration (B : Nat) (ps : List Pair) :
    (ps.map encodePair).foldr (fun p n => max (pairCostCode B p) n) 0 =
      ps.foldr (fun p n => max (cost B p) n) 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons,List.foldr_cons,pairCalibration,ih]

theorem alphabetCalibration (B : Nat) (ops : List LowerOperand) :
    alphabetCode B (ops.map LowerOperand.code) = onAlphabet B ops := by
  unfold alphabetCode onAlphabet familyCost
  rw [labelsCalibration,pairTapeCalibration,foldCalibration]

theorem budgetCalibration (B r : Nat) (terms : List WeightedOperand) :
    cutoffCode B r (terms.map encodeWeighted) = comparisonCeiling B r terms := by
  have encode : (terms.map encodeWeighted).map Prod.snd =
      (terms.map Prod.snd).map LowerOperand.code := by
    simp only [List.map_map,Function.comp_def,encodeWeighted]
  unfold cutoffCode comparisonCeiling budgetAlphabet
  rw [budgetCodeExact.2,encode,codeCalibration.2.2,alphabetCalibration]

theorem exactRawComparisonCeilingCalibration : ExactRawComparisonCeilingCalibration :=
  ⟨labelCalibration,pairCalibration,alphabetCalibration,budgetCalibration⟩

end LogicLineages.PermittedControl.ActualRawComparisonCeiling
