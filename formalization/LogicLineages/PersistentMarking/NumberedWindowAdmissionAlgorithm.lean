module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAdmissionAlgorithm
open NumberedWindowAnnotationAlgorithm (annotations arrow)
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowFieldAlgorithm (unpackNode)

abbrev Window := List Nat × List Nat
abbrev Row := Bool × Bool

def termParts (w : Window) (prev : List Row) (tag : Nat) (fs : List Nat) : Bool :=
  let val (i : Nat) := fs.getD i 0
  let ty (i : Nat) := w.1.contains (val i)
  let hd (i : Nat) := w.2.contains (val i)
  let tm (i : Nat) := (prev.getD (val i) (false,false)).1
  let ar (i : Nat) := (prev.getD (val i) (false,false)).2
  match tag with
  | 0 | 1 | 3 => ty 0
  | 2 => w.1.contains (arrow (val 0) (annotations (val 1)).1) && ty 0 && tm 1
  | 4 => hd 0 && ar 1
  | 5 => hd 0 && ty 1 && ar 3 && ar 4
  | 6 => ty 1 && ty 0 && tm 2 && tm 3
  | _ => false

def termNext (w : Window) (n : Nat) (prev : List Row) : Bool :=
  (unpackNode n).any (fun p => termParts w prev p.1 p.2)

def argsNext : Nat → List Row → Bool
  | 0, _ => true
  | n+1, prev => (decode n).any (fun p =>
    (prev.getD p.1 (false,false)).1 && (prev.getD p.2 (false,false)).2)

def table (w : Window) : Nat → List Row
  | 0 => []
  | n+1 => let prev := table w n; prev ++ [(termNext w n prev, argsNext n prev)]

def rawBits (w : Window) (n : Nat) : Row :=
  (termNext w n (table w n), argsNext n (table w n))

def bits (w : Window) (n : Nat) : Row :=
  let valid := NumberedWindowSyntaxAlgorithm.syntaxBits n
  let result := rawBits w n
  (valid.1 && result.1, valid.2 && result.2)

end LogicLineages.PersistentMarking.NumberedWindowAdmissionAlgorithm
