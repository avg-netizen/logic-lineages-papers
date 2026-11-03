module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTable
open Source NumberedNumericDecoding

def lookup (previous : List Bool) (value : Nat) : Bool := (previous[value]?).getD false

def codeNext (n : Nat) (previous : List Bool) (value : Nat) : Bool :=
  let tag := (Nat.unpair value).1
  let payload := (Nat.unpair value).2
  match tag with
  | 0 => true
  | 1 => (decodeType (Nat.unpair payload).1).isSome && lookup previous (Nat.unpair payload).2
  | 2 => (decodeType (Nat.unpair payload).1).isSome &&
      lookup previous (Nat.unpair (Nat.unpair payload).2).1 && lookup previous (Nat.unpair (Nat.unpair payload).2).2
  | 3 => (decodeType payload).isSome
  | 4 => (decodeHeadNumber n (Nat.unpair payload).1).isSome && lookup previous (Nat.unpair payload).2
  | 5 =>
      let p1 := (Nat.unpair payload).2
      let p2 := (Nat.unpair p1).2
      let p3 := (Nat.unpair p2).2
      let p4 := (Nat.unpair p3).2
      (decodeHeadNumber n (Nat.unpair p1).1).isSome && (decodeType (Nat.unpair p2).1).isSome &&
        lookup previous (Nat.unpair p3).1 && (decodeTypes (Nat.unpair p4).1).isSome && lookup previous (Nat.unpair p4).2
  | 6 => decide (payload=0)
  | 7 => (decodeType (Nat.unpair payload).1).isSome &&
      lookup previous (Nat.unpair (Nat.unpair payload).2).1 && lookup previous (Nat.unpair (Nat.unpair payload).2).2
  | _ => false

def codeTable (n bound : Nat) : Nat → List Bool
  | 0 => List.replicate (bound+1) false
  | fuel+1 => (List.range (bound+1)).map (codeNext n (codeTable n bound fuel))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTable
