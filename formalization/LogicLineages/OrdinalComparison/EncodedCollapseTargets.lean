module
public import LogicLineages.OrdinalComparison.EncodedCollapseDefinitions
public import LogicLineages.OrdinalComparison.EncodedDescentTargets
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section

/-! Independent full source cor:closed-evaluation contract, paper05 lines233–244.
All finite inputs use the fixed raw ordinal codec. The numerical step, first
finite point, exact source replacement count, totality of the concrete partial
program, and actual Computable certificate must all be proved. No arbitrary
search-success, termination, computability or collapse-agreement premise is
permitted. The source's closed ordinal is calibrated by actualCollapse, not
defined to be this program's output. -/

namespace LogicLineages.OrdinalComparison.Targets

def EncodedTrajectoryCorrect : Prop :=
  ∀ a : NONote, ∀ k : Nat, k ≤ actualReplacementCount a.1.repr →
    ONote.NF (rawNoteDecode (encodedStateAfter (rawNoteEncode a.1) k)) ∧
    (rawNoteDecode (encodedStateAfter (rawNoteEncode a.1) k)).repr =
      (actualDescentStep^[k]) a.1.repr

def EncodedFirstFiniteCorrect : Prop :=
  ∀ a : NONote,
    actualReplacementCount a.1.repr ∈ encodedTerminalSearch (rawNoteEncode a.1) ∧
    encodedFiniteValue (encodedStateAfter (rawNoteEncode a.1)
      (actualReplacementCount a.1.repr)) = actualTerminalValue a.1.repr

def EncodedCollapsePartialRecursive : Prop := Partrec encodedCollapsePartial

def EncodedCollapseTotal : Prop := ∀ n : Nat, (encodedCollapsePartial n).Dom

def EncodedCollapseSourceCorrect : Prop :=
  ∀ a : NONote, encodedCollapseValue (rawNoteEncode a.1) = actualCollapse a.1.repr

def EncodedCollapseComputable : Prop := Computable encodedCollapseValue

def FullEncodedClosedEvaluation : Prop :=
  EncodedFiniteCorrect ∧ EncodedDescentStepCorrect ∧ EncodedDescentStepFiniteFixed ∧
  EncodedStateAfterPrimitiveRecursive ∧ EncodedTrajectoryCorrect ∧ EncodedFirstFiniteCorrect ∧
  EncodedCollapsePartialRecursive ∧ EncodedCollapseTotal ∧ EncodedCollapseSourceCorrect ∧
  EncodedCollapseComputable

end LogicLineages.OrdinalComparison.Targets
