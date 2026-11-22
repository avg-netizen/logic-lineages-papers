module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapes
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (RawTerm groupRaw groupTyped encodeTerm)
open ActualRawCanonicalNodeMetadata (labelsCode)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Answer)
open ActualFiniteFullValueGuards (pairs patterns)

def answerTapes : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => [0,1,2].flatMap (fun a => (answerTapes n).map (List.cons a))

def pairWidth (terms : List RawTerm) : Nat :=
  let n := (labelsCode terms).length
  n * n

def candidateTapes (terms : List RawTerm) : List (List Nat) := answerTapes (pairWidth terms)

def ExactRawAnswerTapeEnumeration : Prop :=
  (∀ n : Nat, answerTapes n = (patterns n).map (List.map Answer.code)) ∧
  ∀ (n : Nat) (tape : List Nat), tape ∈ answerTapes n →
    tape.length = n ∧ ∀ a ∈ tape, a < 3

def ExactCanonicalAnswerPairs : Prop :=
  (∀ terms : List WeightedOperand,
    pairWidth (terms.map encodeTerm) = (pairs (labels terms)).length ∧
    candidateTapes (terms.map encodeTerm) = (patterns (pairs (labels terms)).length).map (List.map Answer.code)) ∧
  ∀ ts : List WeightedOperand,
    let grouped := groupTyped ts
    let raw := groupRaw (ts.map encodeTerm)
    pairWidth raw = (pairs (labels grouped)).length ∧
    candidateTapes raw = (patterns (pairs (labels grouped)).length).map (List.map Answer.code)

def ExactRawAnswerTapeEffectivity : Prop :=
  Primrec answerTapes ∧ Primrec pairWidth ∧ Primrec candidateTapes

def FullActualRawCanonicalAnswerTapes : Prop :=
  ExactRawAnswerTapeEnumeration ∧ ExactCanonicalAnswerPairs ∧ ExactRawAnswerTapeEffectivity

end LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapes
