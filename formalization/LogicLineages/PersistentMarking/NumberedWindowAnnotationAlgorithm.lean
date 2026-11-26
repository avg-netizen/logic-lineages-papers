module

public import LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowSyntaxAlgorithm (syntaxBits headBit)

abbrev Row := Nat × List Nat

def arrow (dom cod : Nat) := pair dom cod + 1

def headParts (tag payload : Nat) : Row :=
  match tag with
  | 0 => (0,[])
  | 1 => (arrow 0 0,[])
  | 2 => (arrow 0 (arrow payload (arrow payload payload)),[])
  | 3 => (arrow 0 (arrow (arrow 0 (arrow payload payload)) (arrow payload payload)),[])
  | 4 => ((decode payload).map (fun p => (p.2,[arrow p.1 p.2,p.1]))).getD default
  | 5 => ((decode payload).map (fun p => (0,List.replicate p.2 0))).getD default
  | _ => default

def declaration (n : Nat) : Row :=
  ((decode n).map (fun p => headParts p.1 p.2)).getD default

def termParts (table : List Row) (tag : Nat) (fs : List Nat) : Nat :=
  match tag with
  | 0 | 1 | 3 => fs.getD 0 0
  | 2 => arrow (fs.getD 0 0) (table.getD (fs.getD 1 0) default).1
  | 4 => (declaration (fs.getD 0 0)).1
  | 5 | 6 => fs.getD 1 0
  | _ => 0

def termNext (n : Nat) (t : List Row) :=
  ((unpackNode n).map (fun p => termParts t p.1 p.2)).getD 0

def argsNext : Nat → List Row → List Nat
  | 0,_ => []
  | n+1,t => ((decode n).map (fun p => (t.getD p.1 default).1 :: (t.getD p.2 default).2)).getD []

def table : Nat → List Row
  | 0 => []
  | n+1 => let t := table n; t ++ [(termNext n t,argsNext n t)]

def annotations (n : Nat) : Row := (termNext n (table n),argsNext n (table n))

def headOutput (n : Nat) : Option Row := if headBit n then some (declaration n) else none

def output (n : Nat) : Option Nat × Option (List Nat) :=
  let valid := syntaxBits n
  let row := annotations n
  (if valid.1 then some row.1 else none, if valid.2 then some row.2 else none)

end LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm
