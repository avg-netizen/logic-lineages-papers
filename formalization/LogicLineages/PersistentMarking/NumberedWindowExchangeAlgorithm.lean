module

public import LogicLineages.PersistentMarking.NumberedWindowExchangeAtoms

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowExchangeAlgorithm
open NumberedWindowExchangeAtoms (HeadPairs allowed bag)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowPairAlgorithm (pair decode)
abbrev Row := Bool × Bool

def parts (hp : HeadPairs) (prev : List Row) (i j : Nat) (fs gs : List Nat) : Bool :=
  let x (a : Nat) := fs.getD a 0
  let y (a : Nat) := gs.getD a 0
  let equal (a : Nat) := x a == y a
  let related (a : Nat) := prev.getD (pair (x a) (y a)) (false,false)
  let heads := allowed hp (x 0) (y 0)
  if i != j then false else
    match i with
    | 2 => equal 0 && (related 1).1
    | 4 =>
      (heads && ((NumberedWindowAnnotationAlgorithm.declaration (x 0)).1 ==
        (NumberedWindowAnnotationAlgorithm.declaration (y 0)).1) && bag (x 1) (y 1)) ||
      (equal 0 && (related 1).2)
    | 5 => equal 1 && equal 2 &&
        ((heads && bag (x 3) (y 3) && equal 4) ||
        (equal 0 && (((related 3).2 && equal 4) || (equal 3 && (related 4).2))))
    | 6 => equal 0 && equal 1 &&
        (((related 2).1 && equal 3) || (equal 2 && (related 3).1))
    | _ => false

def termNext (hp : HeadPairs) (prev : List Row) (a b : Nat) :=
  (unpackNode a).any (fun p => (unpackNode b).any (fun q => parts hp prev p.1 q.1 p.2 q.2))

def argsNext (prev : List Row) : Nat → Nat → Bool
  | a+1,b+1 => (decode a).any (fun p => (decode b).any (fun q =>
      ((prev.getD (pair p.1 q.1) (false,false)).1 && p.2 == q.2) ||
      (p.1 == q.1 && (prev.getD (pair p.2 q.2) (false,false)).2)))
  | _,_ => false

def next (hp : HeadPairs) (prev : List Row) (key : Nat) : Row :=
  ((decode key).map (fun p => (termNext hp prev p.1 p.2,argsNext prev p.1 p.2))).getD (false,false)

def table (hp : HeadPairs) : Nat → List Row
  | 0 => []
  | n+1 => let t := table hp n; t ++ [next hp t n]

def row (hp : HeadPairs) (a b : Nat) := next hp (table hp (pair a b)) (pair a b)

def bits (hp : HeadPairs) (a b : Nat) : Row :=
  let x := NumberedWindowSyntaxAlgorithm.syntaxBits a
  let y := NumberedWindowSyntaxAlgorithm.syntaxBits b
  let r := row hp a b
  (x.1 && y.1 && r.1,x.2 && y.2 && r.2)
end LogicLineages.PersistentMarking.NumberedWindowExchangeAlgorithm
