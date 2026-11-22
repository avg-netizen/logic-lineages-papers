module
public import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundTargets
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeCalibrationProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingSum ActualZeroClassCommonTail ActualZeroEdgeConstantShift
open ActualZeroEdgeAlphabet ActualZeroEdgeAlphabetCode ActualSyntaxChargeBudget ActualShortCountCleanup
open SelectedCountOnlyClass (omegaSquareNote prefixTarget)
open Targets (countCoreConstant)

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

private theorem correctionLiteral (op : LowerOperand) :
    correctionBoundCode op.code = correctionBound op := by
  cases op with
  | coordinate rank => rfl
  | ordinary rank field => rfl
  | count rank lam mu =>
      simp [correctionBoundCode,correctionBound,LowerOperand.code,longFieldCode,
        normal_norm_code,countCoreConstant]

private theorem shortLiteral (op : LowerOperand) : shortLengthCode op.code = shortLength op := by
  cases op with
  | coordinate rank => rfl
  | ordinary rank field => rfl
  | count rank lam mu => rfl

private theorem correctionMaxLiteral (alphabet : List LowerOperand) :
    correctionMaxCode (alphabet.map LowerOperand.code) = correctionMaximum alphabet :=
  maxLiteral LowerOperand.code correctionBoundCode correctionBound alphabet correctionLiteral

private theorem prefixShortMaxLiteral (alphabet : List LowerOperand) :
    prefixShortMaxCode (alphabet.map LowerOperand.code) = prefixShortMaximum alphabet := by
  unfold prefixShortMaxCode prefixShortMaximum
  rw [prefixChoicesLiteral]
  exact maxLiteral encodePrefix (fun p : PrefixCode => shortGapLengthCode p.2.1 p.2.2)
    (fun p : PrefixLabel => shortGapLength p.lam p.eta) (prefixCandidates alphabet) (fun _ => rfl)

private theorem cleanupMaxLiteral (alphabet : List LowerOperand) :
    cleanupMaxCode (alphabet.map LowerOperand.code) = cleanupMaximum alphabet := by
  unfold cleanupMaxCode cleanupMaximum
  rw [ActualZeroEdgeAlphabetCode.codeCalibration.1 alphabet]
  exact maxLiteral LowerOperand.code shortLengthCode shortLength (expand alphabet) shortLiteral

private theorem edgeFactorLiteral (alphabet : List LowerOperand) :
    edgeFactorCode (alphabet.map LowerOperand.code) = edgeFactor alphabet := by
  unfold edgeFactorCode edgeFactor
  rw [correctionMaxLiteral,prefixShortMaxLiteral,cleanupMaxLiteral]

private theorem massLiteral (terms : List WeightedOperand) :
    syntaxMassCode (terms.map encodeWeighted) = syntaxMass terms := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      change t.1.natAbs + syntaxMassCode (terms.map encodeWeighted) = t.1.natAbs + syntaxMass terms
      rw [ih]

theorem suppliedLiteral (budget : Nat) (c : Int) (terms : List WeightedOperand) :
    signCeilingAtBudgetCode budget c (terms.map encodeWeighted) = signCeilingAtBudget budget c terms := by
  have keys : (terms.map encodeWeighted).map Prod.snd = (terms.map Prod.snd).map LowerOperand.code := by
    simp only [List.map_map,Function.comp_def,encodeWeighted]
  unfold signCeilingAtBudgetCode signCeilingAtBudget depthAlphabet
  rw [keys,ActualZeroEdgeAlphabetCode.codeCalibration.2.2,massLiteral]
  dsimp only
  rw [edgeFactorLiteral,correctionMaxLiteral]

theorem inputLiteral (r : Nat) (c : Int) (terms : List WeightedOperand) :
    inputSignBoundCode r c (terms.map encodeWeighted) = signCeilingAtBudget (syntaxBudget r terms) c terms := by
  unfold inputSignBoundCode
  rw [budgetCodeExact.2 r terms,suppliedLiteral]

theorem codeCalibration : CodeCalibration := ⟨suppliedLiteral,inputLiteral⟩

end LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
