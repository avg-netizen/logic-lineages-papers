module
public import LogicLineages.OrdinalComparison.EncodedCompensatedCountDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedCompensatedStatePrimitiveRecursive : Prop :=
  Primrec (fun p : (Nat × Nat) × Nat => encodedCompensatedState p.1.1 p.1.2 p.2)

def EncodedCompensatedTrajectoryCorrect : Prop :=
  ∀ c : Nat, ∀ a : NONote, ∀ k : Nat,
    k ≤ actualControlledCount (compensatedPrefixControl c) a.1.repr →
      ONote.NF (rawNoteDecode (encodedCompensatedState c (rawNoteEncode a.1) k)) ∧
      (rawNoteDecode (encodedCompensatedState c (rawNoteEncode a.1) k)).repr=
        actualControlledStateAfter (compensatedPrefixControl c) a.1.repr k

def EncodedCompensatedFirstFiniteCorrect : Prop :=
  ∀ c : Nat, ∀ a : NONote,
    actualControlledCount (compensatedPrefixControl c) a.1.repr ∈
      encodedCompensatedSearch c (rawNoteEncode a.1)

def EncodedCompensatedCountPartialRecursive : Prop := Partrec₂ encodedCompensatedCountPartial

def EncodedCompensatedCountTotal : Prop := ∀ c n : Nat, (encodedCompensatedCountPartial c n).Dom

def EncodedCompensatedCountCorrect : Prop :=
  ∀ c : Nat, ∀ a : NONote, encodedCompensatedCountValue c (rawNoteEncode a.1)=
    actualControlledCount (compensatedPrefixControl c) a.1.repr

def EncodedCompensatedCountComputable : Prop := Computable₂ encodedCompensatedCountValue

end LogicLineages.OrdinalComparison.Targets
