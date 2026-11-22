module
public import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorTargets
public import LogicLineages.PermittedControl.ActualRawSignedCleanupTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualSymbolicZeroSuccessor ActualZeroSuccessorMarkedClass ActualZeroSuccessorPrefixPlan
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualRawSignedCleanup (cleanupCode)
open SelectedCountOnlyClass (omegaSquareNote)
open ActualCountCoreLabels (rawTag)
open ConcreteCountPairReplacement (replacementCode)
open FieldComparison (shortGapLengthCode)

abbrev MarkCode := WeightedCode × Bool
abbrev PlanCode := Nat × Nat × Nat
abbrev PrefixCode := Nat × Nat × Nat × Int

def encodeMark (m : Marked) : MarkCode := (encodeWeighted m.1,m.2)
def encodePrefix (p : PrefixSyntax) : PrefixCode :=
  (p.rank,rawNoteEncode p.lam.1,rawNoteEncode p.eta.1,p.weight)

def encodePlan : CountPlan → Option PlanCode
  | .invalid => none
  | .identity => some (0,0,0)
  | .short eta k => some (1,rawNoteEncode eta.1,k)
  | .survives eta => some (1,rawNoteEncode eta.1,0)

def etaCode (mu : Nat) : Nat := ordinalAddCode mu (rawNoteEncode omegaSquareNote.1)

def coreCode (mu : Nat) : Int := 1 - (((rawNormCode mu + 1) / 2 : Nat) : Int)

/-- A nonempty plan is either the genuine identity prefix (first flag
zero) or its real canonical endpoint and short-prefix length. Long and
short original intervals are not conflated. -/
def planCode (p : Nat × Nat) : Option PlanCode :=
  let tag := rawTag p.1 p.2
  if tag = 2 then some (0,0,0)
  else if tag = 3 then
    let eta := etaCode p.2
    some (1,eta,shortGapLengthCode p.1 eta)
  else none

def endpoints (op : LowerOperandCode) : Nat × Nat := op.2.2.2.2

def shiftOneCode (m : MarkCode) : Option Int :=
  if m.2 then
    if m.1.2.1 = 2 then
      (planCode (endpoints m.1.2)).map fun plan =>
        m.1.1 * (coreCode (endpoints m.1.2).2 + (plan.2.2 : Int))
    else if m.1.2.1 = 1 then some 0 else none
  else some 0

def shiftAddCode (a b : Option Int) : Option Int := do
  let s ← a
  let t ← b
  pure (s+t)

def shiftsCode (ms : List MarkCode) : Option Int :=
  ms.foldr (fun m acc => shiftAddCode (shiftOneCode m) acc) (some 0)

def markedPrefixCode (m : MarkCode) : Option PrefixCode :=
  if m.2 then
    if m.1.2.1 = 2 then
      (planCode (endpoints m.1.2)).bind fun plan =>
        if plan.1 = 1 ∧ plan.2.2 = 0 then
          some (m.1.2.2.1,(endpoints m.1.2).1,plan.2.1,m.1.1)
        else none
    else none
  else none

def cohortCode (ms : List MarkCode) : List PrefixCode := ms.filterMap markedPrefixCode

def leastStepCode (p : PrefixCode) (tailBest : Option PrefixCode) : Option PrefixCode :=
  match tailBest with
  | none => some p
  | some q => if p.1 ≤ q.1 then some p else some q

/-- Right fold with <= chooses the *first original occurrence* on a
tie, rather than a fresh endpoint ordering. -/
def leastCode (ps : List PrefixCode) : Option PrefixCode := ps.foldr leastStepCode none

def outsideCode (ms : List MarkCode) : List WeightedCode :=
  (ms.filter fun m => decide (m.1.1 ≠ 0) && !m.2).map Prod.fst

def anchorCode (a : PrefixCode) (w : Int) : WeightedCode :=
  (w,(2,a.1,(1,0,a.2.1,a.2.2.1)))

def moveOneCode (a p : PrefixCode) : List WeightedCode :=
  let w := p.2.2.2
  let bare := anchorCode a w
  if p.1 = a.1 then [bare]
  else [bare,(-w,replacementCode a.1 ((p.2.1,p.2.2.1),(a.2.1,a.2.2.1)))]

def movedCode (a : Option PrefixCode) (ps : List PrefixCode) : List WeightedCode :=
  match a with
  | none => []
  | some best => ps.flatMap (moveOneCode best)

/-- Only post-decoration static work. No evaluator, f, actual valuation,
or read-success approximation is called here. -/
def markedSuccessorCode (p : Int × List MarkCode) : Option RawSyntax := do
  let shift ← shiftsCode p.2
  let ps := cohortCode p.2
  let before := outsideCode p.2 ++ movedCode (leastCode ps) ps
  pure (cleanupCode (p.1+shift,before))

def ExactRawMarkedPlan : Prop :=
  (∀ lam mu : NONote, planCode (rawNoteEncode lam.1,rawNoteEncode mu.1) =
    encodePlan (countPlan lam mu)) ∧
  (∀ m : Marked, shiftOneCode (encodeMark m) = originShift m ∧
    markedPrefixCode (encodeMark m) = (markedPrefix m).map encodePrefix)

def ExactRawMarkedMove : Prop :=
  (∀ ps : List PrefixSyntax, leastCode (ps.map encodePrefix) = (leastSyntax ps).map encodePrefix) ∧
  ∀ (a : Option PrefixSyntax) (ps : List PrefixSyntax),
    movedCode (a.map encodePrefix) (ps.map encodePrefix) = (movedSyntax a ps).map encodeWeighted

def ExactRawMarkedSuccessor : Prop :=
  ∀ (constant : Int) (ms : List Marked),
    markedSuccessorCode (constant,ms.map encodeMark) =
      (successorFromMarks constant ms).map encodeSyntax

def ExactRawMarkedSuccessorEffectivity : Prop :=
  Primrec markedSuccessorCode

def FullActualRawMarkedZeroSuccessor : Prop :=
  ExactRawMarkedPlan ∧ ExactRawMarkedMove ∧ ExactRawMarkedSuccessor ∧ ExactRawMarkedSuccessorEffectivity

end LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
