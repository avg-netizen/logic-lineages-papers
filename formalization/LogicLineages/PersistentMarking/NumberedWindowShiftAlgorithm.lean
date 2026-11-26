module

public import LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowShiftAlgorithm
open NumberedWindowFieldAlgorithm (packNode unpackNode)
open NumberedWindowPairAlgorithm (pair decode)

abbrev Row := Nat × Nat
abbrev Table := List (List Row)

def earlier (t : Table) (code offset : Nat) : Row :=
  (t.getD code []).getD offset (0,0)

def termParts (t : Table) (amount cutoff offset tag : Nat) (fs : List Nat) : Nat :=
  let atField (i : Nat) := fs.getD i 0
  let tm (i : Nat) := (earlier t (atField i) offset).1
  let ar (i : Nat) := (earlier t (atField i) offset).2
  match tag with
  | 0 => packNode 0 fs
  | 1 =>
    let i := atField 1
    packNode 1 [atField 0,if i < cutoff + offset then i else i + amount]
  | 2 => packNode 2 [atField 0,(earlier t (atField 1) (offset+1)).1]
  | 3 => packNode 3 fs
  | 4 => packNode 4 [atField 0,ar 1]
  | 5 => packNode 5 [atField 0,atField 1,atField 2,ar 3,ar 4]
  | 6 => packNode 6 [atField 0,atField 1,tm 2,tm 3]
  | _ => 0

def termNext (amount cutoff offset n : Nat) (t : Table) : Nat :=
  ((unpackNode n).map (fun p => termParts t amount cutoff offset p.1 p.2)).getD 0

def argsNext (offset : Nat) : Nat → Table → Nat
  | 0,_ => 0
  | n+1,t => ((decode n).map (fun p =>
      pair (earlier t p.1 offset).1 (earlier t p.2 offset).2 + 1)).getD 0

def next (amount cutoff offset n : Nat) (t : Table) : Row :=
  (termNext amount cutoff offset n t,argsNext offset n t)

def layer (amount cutoff bound n : Nat) (t : Table) : List Row :=
  (List.range (bound+1)).map (fun offset => next amount cutoff offset n t)

def table (amount cutoff bound : Nat) : Nat → Table
  | 0 => []
  | n+1 =>
    let t := table amount cutoff bound n
    t ++ [layer amount cutoff bound n t]

def computed (amount cutoff bound n offset : Nat) : Row :=
  next amount cutoff offset n (table amount cutoff bound n)

def output (amount cutoff n : Nat) : Option Nat × Option Nat :=
  let row := computed amount cutoff n n 0
  let valid := NumberedWindowSyntaxAlgorithm.syntaxBits n
  (if valid.1 then some row.1 else none, if valid.2 then some row.2 else none)

end LogicLineages.PersistentMarking.NumberedWindowShiftAlgorithm
