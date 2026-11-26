module
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroReplayTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodeProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroReplay
open ActualRawCanonicalNode (groupedCode exactRawOrderedNode)
open ActualCanonicalOperandGrouping (encodeTerm groupRaw groupTyped exactCanonicalTape)
open ActualRawSignedStaticCeiling (encodeSyntax RawSyntax)
open ActualCanonicalZeroTrace (replay eraseState exactCanonicalTraceReplay)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualFullLabelPairGuards (Answer)

theorem exactRawCanonicalZeroStep : ExactRawCanonicalZeroStep := by
  intro s answers
  change (groupedCode (s.constant,groupRaw (s.terms.map encodeTerm),answers.map Answer.code)).2 = _
  rw [← exactCanonicalTape.1 s.terms,exactRawOrderedNode] <;> rfl

private theorem foldNone (answers : SequenceCode) :
    answers.foldl advanceCode none = none := by
  induction answers with
  | nil => rfl
  | cons head tail ih => exact ih

theorem exactRawCanonicalZeroReplay : ExactRawCanonicalZeroReplay := by
  intro s answers
  induction answers generalizing s with
  | nil => rfl
  | cons a tail ih =>
    change (encodeAnswers tail).foldl advanceCode
        (stepCode (encodeSyntax s,a.map Answer.code)) =
      (((canonicalSuccessor s.constant s.terms a).bind (replay tail)).map encodeSyntax)
    rw [exactRawCanonicalZeroStep]
    cases h : canonicalSuccessor s.constant s.terms a with
    | none =>
      change (encodeAnswers tail).foldl advanceCode none = none
      exact foldNone _
    | some next =>
      change replayCode (encodeAnswers tail,encodeSyntax next) = (replay tail next).map encodeSyntax
      exact ih next

theorem exactRawReplayActualWitness : ExactRawReplayActualWitness := by
  intro f B selected ρ r top s t answers witness
  have typed := (exactCanonicalTraceReplay f B selected ρ r top s t answers witness).1
  rw [exactRawCanonicalZeroReplay,typed] <;> rfl

end LogicLineages.PermittedControl.ActualRawCanonicalZeroReplay
