module
public import LogicLineages.PermittedControl.ActualEffectiveGlobalTailTargets
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeCalibrationProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveGlobalTail
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualZeroClassCommonTail ActualZeroEdgeAlphabetCode ActualZeroEdgeAlphabet
open ActualNodeTailSupply ActualFiniteGlobalTail ActualSyntaxChargeBudget
open SelectedCountOnlyClass (omegaSquareNote prefixTarget)

private theorem prefixChoiceLiteral (op : LowerOperand) :
    prefixChoiceCode op.code = (prefixLabel (1,op)).map encodePrefix := by
  cases op with
  | coordinate rank => rfl
  | ordinary rank field => rfl
  | count rank lam mu =>
      change some (rank,rawNoteEncode lam.1,
          ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode omegaSquareNote.1)) =
        some (rank,rawNoteEncode lam.1,rawNoteEncode (prefixTarget mu).1)
      rw [ordinal_add_note_code mu omegaSquareNote] <;> rfl

private theorem prefixChoicesLiteral (alphabet : List LowerOperand) :
    prefixChoicesCode (alphabet.map LowerOperand.code) =
      (prefixCandidates alphabet).map encodePrefix := by
  induction alphabet with
  | nil => rfl
  | cons op tail ih =>
      cases h : prefixLabel (1,op) with
      | none =>
          simp only [prefixChoicesCode,prefixCandidates,List.map_cons,List.filterMap_cons,
            prefixChoiceLiteral,h,Option.map_none]
          exact ih
      | some p =>
          simp only [prefixChoicesCode,prefixCandidates,List.map_cons,List.filterMap_cons,
            prefixChoiceLiteral,h,Option.map_some]
          exact congrArg (List.cons (encodePrefix p)) ih

private theorem maxLiteral {α β : Type} (encode : α → β) (codeCost : β → Nat) (cost : α → Nat)
    (xs : List α) (lit : ∀ x, codeCost (encode x) = cost x) :
    finiteMax codeCost (xs.map encode) = finiteMax cost xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change max (codeCost (encode x)) (finiteMax codeCost (xs.map encode)) =
        max (cost x) (finiteMax cost xs)
      rw [lit x,ih]

private theorem affordableLiteral (B : Nat) (p : PrefixLabel) :
    prefixAffordabilityCode B (encodePrefix p) = prefixAffordability B p := by
  simp only [prefixAffordabilityCode,encodePrefix,prefixAffordability,
    normal_norm_code p.lam,normal_norm_code p.eta]

private theorem pairLiteral (B : Nat) (lo hi : PrefixLabel) :
    pairTailCode B (encodePrefix lo) (encodePrefix hi) = labelPairTail B lo hi := rfl

private theorem labelsLiteral (B : Nat) (labels : List PrefixLabel) :
    labelsTailCode B (labels.map encodePrefix) =
      max (finiteMax (prefixAffordability B) labels)
        (finiteMax (fun lo => finiteMax (labelPairTail B lo) labels) labels) := by
  have inner (lo : PrefixLabel) :
      finiteMax (pairTailCode B (encodePrefix lo)) (labels.map encodePrefix) =
        finiteMax (labelPairTail B lo) labels :=
    maxLiteral encodePrefix (pairTailCode B (encodePrefix lo)) (labelPairTail B lo) labels
      (pairLiteral B lo)
  unfold labelsTailCode
  rw [maxLiteral encodePrefix (prefixAffordabilityCode B) (prefixAffordability B) labels
    (affordableLiteral B)]
  rw [maxLiteral encodePrefix (fun lo => finiteMax (pairTailCode B lo) (labels.map encodePrefix))
    (fun lo => finiteMax (labelPairTail B lo) labels) labels inner]

private theorem annotationLiteral (alphabet : List LowerOperand) :
    finiteMax annotationBoundCode (alphabet.map LowerOperand.code) =
      annotationTail (unitTerms alphabet) := by
  simp only [annotationTail,annotationTailCode,unitTerms,List.map_map,Function.comp_def]
  exact maxLiteral LowerOperand.code annotationBoundCode (fun op => annotationBoundCode op.code)
    alphabet (fun _ => rfl) |>.trans
    (maxLiteral (fun op : LowerOperand => encodeWeighted (1,op))
      (fun w : WeightedCode => annotationBoundCode w.2)
      (fun op => annotationBoundCode op.code) alphabet (fun _ => rfl)).symm

theorem alphabetLiteral (B : Nat) (alphabet : List LowerOperand) :
    alphabetTailCode B (alphabet.map LowerOperand.code) = alphabetTail B alphabet := by
  have labels : prefixLabels (unitTerms alphabet) = prefixCandidates alphabet := by
    simp only [prefixLabels,unitTerms,prefixCandidates,List.filterMap_map,Function.comp_def]
  unfold alphabetTailCode alphabetTail nodeTail commonTail
  rw [annotationLiteral,prefixChoicesLiteral,labelsLiteral,labels]

theorem suppliedLiteral (B budget : Nat) (alphabet : List LowerOperand) :
    suppliedTailCode B budget (alphabet.map LowerOperand.code) =
      alphabetTail B ((List.range (budget+1)).flatMap (fun d => expandSteps d alphabet)) := by
  unfold suppliedTailCode
  rw [ActualZeroEdgeAlphabetCode.codeCalibration.2.2 budget alphabet,alphabetLiteral]

theorem inputLiteral (B r : Nat) (terms : List WeightedOperand) :
    inputTailCode B r (terms.map encodeWeighted) =
      alphabetTail B ((List.range (syntaxBudget r terms+1)).flatMap
        (fun d => expandSteps d (terms.map Prod.snd))) := by
  have literals : (terms.map encodeWeighted).map Prod.snd = (terms.map Prod.snd).map LowerOperand.code := by
    simp only [List.map_map,Function.comp_def,encodeWeighted]
  unfold inputTailCode
  rw [budgetCodeExact.2 r terms,literals,suppliedLiteral]

theorem codeCalibration : CodeCalibration := ⟨alphabetLiteral,suppliedLiteral,inputLiteral⟩

end LogicLineages.PermittedControl.ActualEffectiveGlobalTail
