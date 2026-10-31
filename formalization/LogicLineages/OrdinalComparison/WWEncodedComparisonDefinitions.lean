module
public import LogicLineages.OrdinalComparison.WWEncodedScalarDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

abbrev EncodedVector := Nat × List Nat
abbrev EncodedQuery := Bool × EncodedVector × EncodedVector

def positiveComparisonUpTo : Nat → List Nat → List Nat → Bool
  | 0, _, _ => true
  | n+1, a, b => positiveComparisonUpTo n a b &&
      decide (rawComparisonCode (a.getD n 0) (b.getD n 0) ≤ 1)

/-- Actual zero-padded positive-coordinate comparison, never lexicographic. -/
def positiveComparison (a b : List Nat) : Bool :=
  positiveComparisonUpTo (max a.length b.length) a b

/-- True selects WW strict comparison: scalar strict, every positive
coordinate weak. False selects entirely coordinatewise weak comparison. -/
noncomputable def encodedQueryAt (q : EncodedQuery) (xs : List Nat) : Bool :=
  positiveComparison q.2.1.2 q.2.2.2 &&
    if q.1 then decide (encodedScalarValue q.2.1.1 xs < encodedScalarValue q.2.2.1 xs)
    else decide (encodedScalarValue q.2.1.1 xs ≤ encodedScalarValue q.2.2.1 xs)

def normalCodes (a : List NONote) : List Nat := a.map (fun x => rawNoteEncode x.1)

def zeroNote : NONote := ⟨.zero, ONote.NF.zero⟩

noncomputable def positiveNoteAt (a : List NONote) (n : Nat) : Ordinal :=
  (a.getD n zeroNote).1.repr
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
