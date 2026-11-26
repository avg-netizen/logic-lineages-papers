module

public import LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowFieldAlgorithm (unpackNode)

def headParts : Nat → Nat → Bool
  | 0, p | 1, p => p == 0
  | 2, p | 3, p => typeBit p
  | 4, p => (decode p).any (fun q => typeBit q.1 && typeBit q.2)
  | 5, p => (decode p).isSome
  | _, _ => false

def headBit (n : Nat) := (decode n).any (fun q => headParts q.1 q.2)

def termParts (term args : Nat → Bool) : Nat → List Nat → Bool
  | 0, [t,_] | 1, [t,_] => typeBit t
  | 2, [t,q] => typeBit t && term q
  | 3, [t] => typeBit t
  | 4, [g,bs] => headBit g && args bs
  | 5, [g,t,_,bs,es] => headBit g && typeBit t && args bs && args es
  | 6, [s,t,q,a] => typeBit s && typeBit t && term q && term a
  | _, _ => false

abbrev Row := Bool × Bool

def termNext (n : Nat) (prev : List Row) : Bool :=
  (unpackNode n).any (fun p => termParts
    (fun q => (prev.getD q (false,false)).1)
    (fun a => (prev.getD a (false,false)).2) p.1 p.2)

def argsNext : Nat → List Row → Bool
  | 0, _ => true
  | n+1, prev => (decode n).any (fun p =>
    (prev.getD p.1 (false,false)).1 && (prev.getD p.2 (false,false)).2)

def table : Nat → List Row
  | 0 => []
  | n+1 => let prev := table n; prev ++ [(termNext n prev, argsNext n prev)]

def syntaxBits (n : Nat) : Row := (termNext n (table n), argsNext n (table n))
end LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm
