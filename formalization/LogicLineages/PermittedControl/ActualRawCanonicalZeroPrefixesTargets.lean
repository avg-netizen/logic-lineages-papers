module
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroReplayTargets
public import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixes
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualRawCanonicalZeroReplay (AnswerCode SequenceCode stepCode replayCode)
open ActualRawCanonicalAnswerTapes (candidateTapes)
open ActualCanonicalOperandGrouping (groupRaw)

abbrev Candidate := SequenceCode × RawSyntax

def available (s : RawSyntax) : List AnswerCode := candidateTapes (groupRaw s.2)

def extendCandidate (p : Candidate × AnswerCode) : Option Candidate :=
  (stepCode (p.1.2,p.2)).map fun state => (p.1.1 ++ [p.2],state)

def children (entry : Candidate) : List Candidate :=
  (available entry.2).filterMap (fun tape => extendCandidate (entry,tape))

def nextLevel (entries : List Candidate) : List Candidate := entries.flatMap children

def level (start : RawSyntax) : Nat → List Candidate
  | 0 => [([],start)]
  | n+1 => nextLevel (level start n)

def prefixes (fuel : Nat) (start : RawSyntax) : List Candidate :=
  (List.range (fuel+1)).flatMap (level start)

/-- Precisely the structural supplied-answer paths whose next tape
was emitted by that state's own canonical label-pair width, and whose
one zero syntax step succeeded. No actual read or truth assertions. -/
inductive CandidatePath (start : RawSyntax) : SequenceCode → RawSyntax → Prop where
  | nil : CandidatePath start [] start
  | snoc {tapes : SequenceCode} {s t : RawSyntax} {answer : AnswerCode} :
      CandidatePath start tapes s →
      answer ∈ available s →
      stepCode (s,answer) = some t →
      CandidatePath start (tapes ++ [answer]) t

def ExactRawZeroPrefixLevels : Prop :=
  ∀ (start : RawSyntax) (n : Nat) (entry : Candidate),
    entry ∈ level start n ↔ CandidatePath start entry.1 entry.2 ∧ entry.1.length = n

def ExactRawZeroPrefixEnumeration : Prop :=
  ∀ (fuel : Nat) (start : RawSyntax) (entry : Candidate),
    entry ∈ prefixes fuel start ↔ CandidatePath start entry.1 entry.2 ∧ entry.1.length ≤ fuel

def ExactRawZeroPrefixReplay : Prop :=
  ∀ (fuel : Nat) (start : RawSyntax) (entry : Candidate),
    entry ∈ prefixes fuel start →
      replayCode (entry.1,start) = some entry.2 ∧ entry.1.length ≤ fuel

def ExactRawZeroPrefixEffectivity : Prop :=
  Primrec available ∧ Primrec nextLevel ∧ Primrec₂ level ∧ Primrec₂ prefixes

def FullActualRawCanonicalZeroPrefixes : Prop :=
  ExactRawZeroPrefixLevels ∧ ExactRawZeroPrefixEnumeration ∧ ExactRawZeroPrefixReplay ∧
    ExactRawZeroPrefixEffectivity

end LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixes
