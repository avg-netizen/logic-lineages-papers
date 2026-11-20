module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm
public import Init.Data.List.Perm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatAlgorithm
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowAnnotationAlgorithm (declaration)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

abbrev Node := Nat × List Nat
abbrev Pair := Nat × Nat
abbrev Partition := List Nat × List Nat × List Nat

def peelParts : Node → Node → Option Pair
  | (2,[s,q]), (2,[t,r]) => if s == t then some (q,r) else none
  | _, _ => none

def peelStep (p : Pair) : Pair :=
  (do
    let q ← unpackNode p.1
    let r ← unpackNode p.2
    peelParts q r).getD p

def peel : Nat → Pair → Pair
  | 0,p => p
  | n+1,p => peelStep (peel n p)

def atomic : Node → Node → Bool
  | (4,[f,bs]), (5,[g,t,_,bt,et]) =>
    f == g && t == (declaration f).1 && bs == bt && et == 0
  | (5,[f,s,k,bs,es]), (5,[g,t,l,bt,et]) =>
    f == g && s == t && decide (l < k) && bs == bt && es == et
  | _, _ => false

def markHere (p : Pair) : Bool :=
  (unpackNode p.1).any (fun q => (unpackNode p.2).any (atomic q))

def mark (q r : Nat) : Bool :=
  (syntaxBits q).1 && (syntaxBits r).1 && markHere (peel q (q,r))

def termCodes (n : Nat) : Option (List Nat) := do
  let codes ← unpack n
  if codes.all (fun c => (syntaxBits c).1) then some codes else none

def argsView (n : Nat) : Option (List Nat) :=
  if (syntaxBits n).2 then unpack n else none

def readPartition (n : Nat) : Option Partition := do
  let (0,[kept,removed,added]) ← unpackNode n | none
  let ks ← termCodes kept
  let rs ← termCodes removed
  let as ← termCodes added
  pure (ks,rs,as)

def replacementLists (qs rs : List Nat) (p : Partition) : Bool :=
  decide (qs.Perm (p.1 ++ p.2.1)) &&
    decide (rs.Perm (p.1 ++ p.2.2)) &&
    !p.2.1.isEmpty &&
    p.2.2.all (fun a => p.2.1.any (fun b => mark b a))

def replacement (q w r : Nat) : Bool :=
  match argsView q, readPartition w, argsView r with
  | some qs, some p, some rs => replacementLists qs rs p
  | _, _, _ => false

end LogicLineages.PersistentMarking.NumberedWindowStatAlgorithm
