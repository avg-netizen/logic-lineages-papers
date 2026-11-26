module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowLexicalAlgorithm
open NumberedWindowAnnotationAlgorithm (annotations arrow declaration)
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowFieldAlgorithm (unpackNode)

/-- The bit records local mismatches, and the remaining slots refer to the enclosing context. -/
abbrev Requirement := Bool × List (Nat × Nat)
abbrev Row := Requirement × Requirement
def empty : Requirement := (true,[])
def slot (i t : Nat) : Requirement := (true,[(i,t)])
def join (a b : Requirement) : Requirement := (a.1 && b.1,a.2 ++ b.2)
def restrict (ok : Bool) (r : Requirement) : Requirement := (ok && r.1,r.2)
def discharge (t : Nat) : List (Nat × Nat) → Requirement
  | [] => empty
  | (0,u)::rs => restrict (u == t) (discharge t rs)
  | (i+1,u)::rs => join (slot i u) (discharge t rs)

def binder (t : Nat) (r : Requirement) := restrict r.1 (discharge t r.2)
def holds (C : Nat → Option Nat) (r : Requirement) :=
  r.1 && r.2.all (fun p => C p.1 == some p.2)

def termParts (table : List Row) (tag : Nat) (fs : List Nat) : Requirement :=
  let val (i : Nat) := fs.getD i 0
  let tm (i : Nat) := (table.getD (val i) default).1
  let ar (i : Nat) := (table.getD (val i) default).2
  let base (j : Nat) := (annotations (val j)).2 == (declaration (val 0)).2
  match tag with
  | 0 | 3 => empty
  | 1 => slot (val 1) (val 0)
  | 2 => binder (val 0) (tm 1)
  | 4 => restrict (base 1) (ar 1)
  | 5 => restrict (base 3) (join (ar 3) (ar 4))
  | 6 => join (restrict ((annotations (val 2)).1 == arrow (val 0) (val 1)) (tm 2))
      (restrict ((annotations (val 3)).1 == val 0) (tm 3))
  | _ => default

def termNext (n : Nat) (t : List Row) : Requirement :=
  ((unpackNode n).map (fun p => termParts t p.1 p.2)).getD default
def argsNext : Nat → List Row → Requirement
  | 0,_ => empty
  | n+1,t => ((decode n).map (fun p => join (t.getD p.1 default).1 (t.getD p.2 default).2)).getD default

def table : Nat → List Row
  | 0 => []
  | n+1 => let t := table n; t ++ [(termNext n t,argsNext n t)]
def requirements (n : Nat) : Row := (termNext n (table n),argsNext n (table n))

def typed (ctx : List Nat) (ty n : Nat) : Bool :=
  (NumberedWindowSyntaxAlgorithm.syntaxBits n).1 && (annotations n).1 == ty &&
    holds (fun i => ctx[i]?) (requirements n).1

end LogicLineages.PersistentMarking.NumberedWindowLexicalAlgorithm
