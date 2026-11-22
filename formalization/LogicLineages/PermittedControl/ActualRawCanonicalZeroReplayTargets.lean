module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeTargets
public import LogicLineages.PermittedControl.ActualCanonicalZeroTraceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroReplay
open ActualRawCanonicalNode (groupedCode)
open ActualCanonicalOperandGrouping (groupRaw)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualCanonicalZeroTrace (replay CanonicalTrace eraseState)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualFullLabelPairGuards (Answer)
open ActualReadChargeIteration (ReadState)

abbrev AnswerCode := List Nat
abbrev SequenceCode := List AnswerCode

def encodeAnswers (answers : List (List Answer)) : SequenceCode :=
  answers.map (List.map Answer.code)

/-- This is symbolic replay of already supplied syntax and answers.
There is no read report (true or false) generated or inserted here. -/
def stepCode (p : RawSyntax × AnswerCode) : Option RawSyntax :=
  (groupedCode (p.1.1,groupRaw p.1.2,p.2)).2

def advanceCode (s : Option RawSyntax) (answers : AnswerCode) : Option RawSyntax :=
  s.bind fun t => stepCode (t,answers)

def replayCode (p : SequenceCode × RawSyntax) : Option RawSyntax :=
  p.1.foldl advanceCode (some p.2)

def ExactRawCanonicalZeroStep : Prop :=
  ∀ (s : SyntaxState) (answers : List Answer),
    stepCode (encodeSyntax s,answers.map Answer.code) =
      (canonicalSuccessor s.constant s.terms answers).map encodeSyntax

def ExactRawCanonicalZeroReplay : Prop :=
  ∀ (s : SyntaxState) (answers : List (List Answer)),
    replayCode (encodeAnswers answers,encodeSyntax s) = (replay answers s).map encodeSyntax

def ExactRawReplayActualWitness : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (s t : ReadState) (answers : List (List Answer)),
    CanonicalTrace f B ρ r top answers s t →
      replayCode (encodeAnswers answers,encodeSyntax (eraseState s)) = some (encodeSyntax (eraseState t))

def ExactRawCanonicalZeroReplayEffectivity : Prop :=
  Primrec stepCode ∧ Primrec₂ advanceCode ∧ Primrec replayCode

def FullActualRawCanonicalZeroReplay : Prop :=
  ExactRawCanonicalZeroStep ∧ ExactRawCanonicalZeroReplay ∧ ExactRawReplayActualWitness ∧
    ExactRawCanonicalZeroReplayEffectivity

end LogicLineages.PermittedControl.ActualRawCanonicalZeroReplay
