module

public import LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowCoverAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverBoundsAlgorithm
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

abbrev Measure := Nat × Nat
abbrev Measures := Measure × Measure

def termMeasure (table : List Measures) (tag : Nat) (xs : List Nat) : Measure :=
  let val (i : Nat) := xs.getD i 0
  let tm (i : Nat) := (table.getD (val i) default).1
  let ar (i : Nat) := (table.getD (val i) default).2
  match tag with
  | 0 | 1 => (1,val 1)
  | 2 => ((tm 1).1+1,(tm 1).2)
  | 3 => (1,0)
  | 4 => ((ar 1).1+1,(ar 1).2)
  | 5 => ((ar 3).1 + (ar 4).1 + 1,max (val 2) (max (ar 3).2 (ar 4).2))
  | 6 => ((tm 2).1 + (tm 3).1 + 1,max (tm 2).2 (tm 3).2)
  | _ => (0,0)

def termNext (n : Nat) (table : List Measures) : Measure :=
  ((unpackNode n).map (fun p => termMeasure table p.1 p.2)).getD default

def argsNext : Nat → List Measures → Measure
  | 0, _ => (0,0)
  | n+1, table => ((decode n).map (fun p =>
    let q := (table.getD p.1 default).1
    let r := (table.getD p.2 default).2
    (q.1+1+r.1,max q.2 r.2))).getD default

def table : Nat → List Measures
  | 0 => []
  | n+1 => let prev := table n; prev ++ [(termNext n prev,argsNext n prev)]

def bounds (n : Nat) : Measures := (termNext n (table n), argsNext n (table n))

def cover (heads types : List Nat) (n : Nat) : Option (List Nat) :=
  if (syntaxBits n).1 then
    let b := (bounds n).1
    some (NumberedWindowCoverAlgorithm.grammar heads types b.2 b.1).1
  else none

end LogicLineages.PersistentMarking.NumberedWindowCoverBoundsAlgorithm
