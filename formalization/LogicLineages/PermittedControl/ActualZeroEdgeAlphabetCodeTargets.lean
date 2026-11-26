module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCode
open OrdinalComparison PreparedProjection
open ActualZeroClassCommonTail ActualZeroEdgeAlphabet ConcreteCountPairReplacement
open SelectedCountOnlyClass (omegaSquareNote)

abbrev PrefixCode := Nat × Nat × Nat
abbrev AlphabetCode := List LowerOperandCode

def encodePrefix (p : PrefixLabel) : PrefixCode :=
  (p.rank,rawNoteEncode p.lam.1,rawNoteEncode p.eta.1)

def prefixChoiceCode (op : LowerOperandCode) : Option PrefixCode :=
  if op.1 = 2 then
    some (op.2.1,op.2.2.2.2.1,
      ordinalAddCode op.2.2.2.2.2 (rawNoteEncode omegaSquareNote.1))
  else none

def prefixKeyCode (p : PrefixCode) : LowerOperandCode :=
  (2,p.1,(1,0,p.2.1,p.2.2))

/-- Exact P-versus-Q endpoint order: the candidate lower input's
rank and left endpoint are retained in the literal H code. -/
def pairKeyCode (lower higher : PrefixCode) : LowerOperandCode :=
  replacementCode lower.1 (higher.2,lower.2)

def pairChoiceCode (lower higher : PrefixCode) : Option LowerOperandCode :=
  if lower.1 < higher.1 then some (pairKeyCode lower higher) else none

def prefixChoicesCode (alphabet : AlphabetCode) : List PrefixCode :=
  alphabet.filterMap prefixChoiceCode

def pairChoicesCode (labels : List PrefixCode) : AlphabetCode :=
  labels.flatMap (fun lower => labels.filterMap (pairChoiceCode lower))

def expandCode (alphabet : AlphabetCode) : AlphabetCode :=
  let labels := prefixChoicesCode alphabet
  alphabet ++ (labels.map prefixKeyCode ++ pairChoicesCode labels)

/-- The depth is supplied, not computed from signed syntax. -/
def expandStepsCode (depth : Nat) (alphabet : AlphabetCode) : AlphabetCode :=
  depth.rec alphabet (fun _ next => expandCode next)

def collectCode (budget : Nat) (alphabet : AlphabetCode) : AlphabetCode :=
  (List.range (budget+1)).flatMap (fun depth => expandStepsCode depth alphabet)

/-- Raw programs are total, but typed correspondence is the only
semantic conclusion; invalid candidate codes are not validated. -/
def CodeEffectivity : Prop :=
  Primrec expandCode ∧ Primrec₂ expandStepsCode ∧ Primrec₂ collectCode

def CodeCalibration : Prop :=
  (∀ alphabet : List LowerOperand,
    expandCode (alphabet.map LowerOperand.code) = (expand alphabet).map LowerOperand.code) ∧
  (∀ (depth : Nat) (alphabet : List LowerOperand),
    expandStepsCode depth (alphabet.map LowerOperand.code) =
      (expandSteps depth alphabet).map LowerOperand.code) ∧
  ∀ (budget : Nat) (alphabet : List LowerOperand),
    collectCode budget (alphabet.map LowerOperand.code) =
      ((List.range (budget+1)).flatMap (fun depth => expandSteps depth alphabet)).map LowerOperand.code

def FullActualZeroEdgeAlphabetCode : Prop := CodeEffectivity ∧ CodeCalibration

end LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCode
