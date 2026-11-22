module
public import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
open OrdinalComparison MixedSameRankResidue ConcreteCountPairReplacement
open ActualSymbolicZeroSuccessor ActualZeroSuccessorPrefixPlan

theorem leastCalibration (ps : List PrefixSyntax) :
    leastCode (ps.map encodePrefix) = (leastSyntax ps).map encodePrefix := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change leastStepCode (encodePrefix p) (leastCode (ps.map encodePrefix)) = _
    rw [ih]
    cases found : leastSyntax ps with
    | none => simp only [leastSyntax,found,Option.map_none,leastStepCode,Option.map_some]
    | some best =>
      by_cases smaller : p.rank ≤ best.rank <;> simp [leastSyntax,found,leastStepCode,encodePrefix,smaller]

private theorem replacementLiteral (r0 : Nat) (lp mp lq mq : NONote) :
    replacementCode r0 (intervalPairCodes lp mp lq mq) =
      (replacementOperand r0 lp mp lq mq).code := by
  simp only [replacementCode,intervalPairCodes,replacementOperand,PreparedProjection.LowerOperand.code,FieldComparison.longFieldCode]
  rw [ordinal_sub_note_code,ordinal_add_note_code]

private theorem oneMoveCalibration (a p : PrefixSyntax) :
    moveOneCode (encodePrefix a) (encodePrefix p) = (moveOne a p).map encodeWeighted := by
  have bare : anchorCode (encodePrefix a) p.weight = encodeWeighted (anchorTerm a p.weight) := rfl
  have replacement :
      replacementCode a.rank (intervalPairCodes p.lam p.eta a.lam a.eta) =
      (replacementOperand a.rank p.lam p.eta a.lam a.eta).code := replacementLiteral _ _ _ _ _
  unfold moveOneCode moveOne
  change (if p.rank = a.rank then [anchorCode (encodePrefix a) p.weight]
    else [anchorCode (encodePrefix a) p.weight,
      (-p.weight,replacementCode a.rank (intervalPairCodes p.lam p.eta a.lam a.eta))]) =
    (if p.rank = a.rank then [anchorTerm a p.weight]
      else [anchorTerm a p.weight,movedTerm a p]).map encodeWeighted
  rw [bare,replacement]
  split <;> rfl

theorem moveCalibration (a : Option PrefixSyntax) (ps : List PrefixSyntax) :
    movedCode (a.map encodePrefix) (ps.map encodePrefix) = (movedSyntax a ps).map encodeWeighted := by
  cases a with
  | none => rfl
  | some best =>
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      change moveOneCode (encodePrefix best) (encodePrefix p) ++
        movedCode (some (encodePrefix best)) (ps.map encodePrefix) =
        (moveOne best p ++ movedSyntax (some best) ps).map encodeWeighted
      rw [List.map_append,oneMoveCalibration]
      exact congrArg (List.append ((moveOne best p).map encodeWeighted)) ih

theorem exactRawMarkedMove : ExactRawMarkedMove := ⟨leastCalibration,moveCalibration⟩

end LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
