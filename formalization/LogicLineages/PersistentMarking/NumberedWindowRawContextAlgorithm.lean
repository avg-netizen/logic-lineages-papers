module

public import LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowPairAlgorithm (decode)

abbrev Pair := Nat × Nat
abbrev Frame := Nat × Nat × Nat
abbrev State := Bool × Option Frame
abbrev RawRoot := Nat → Nat → Nat → Bool
abbrev Window := List Nat → Nat → Nat → Bool

def cell : Nat → Option Pair
  | 0 => none
  | n+1 => decode n

def skipPair (p : Option Pair) : Option Pair := do
  let (q,r) ← p
  let (a,qs) ← cell q
  let (b,rs) ← cell r
  if a == b then some (qs,rs) else none

def skipPrefix : Nat → Option Pair → Option Pair
  | 0,p => p
  | i+1,p => skipPrefix i (skipPair p)

def focus (i q r : Nat) : Option Pair := do
  let (q,r) ← skipPrefix i (some (q,r))
  let (a,qs) ← cell q
  let (b,rs) ← cell r
  if qs == rs then some (a,b) else none

def context (tag : Nat) (ws : List Nat) (src dst : Nat × List Nat) : Option Frame :=
  match tag, ws, src, dst with
  | 1, [w], (2,[s,q]), (2,[t,r]) =>
    if s == t then some (q,w,r) else none
  | 2, [i,w], (4,[f,qs]), (4,[g,rs]) =>
    if f == g then (focus i qs rs).map (fun (q,r) => (q,w,r)) else none
  | 3, [i,w], (5,[f,s,k,bs,es]), (5,[g,t,l,bt,et]) =>
    if f == g && s == t && k == l && es == et then
      (focus i bs bt).map (fun (q,r) => (q,w,r))
    else none
  | 4, [i,w], (5,[f,s,k,bs,es]), (5,[g,t,l,bt,et]) =>
    if f == g && s == t && k == l && bs == bt then
      (focus i es et).map (fun (q,r) => (q,w,r))
    else none
  | 5, [w], (6,[s,t,q,a]), (6,[u,v,r,b]) =>
    if s == u && t == v && a == b then some (q,w,r) else none
  | _, _, _, _ => none

def next (tag : Nat) (ws : List Nat) (q r : Nat) : Option Frame := do
  let src ← unpackNode q
  let dst ← unpackNode r
  context tag ws src dst

def tick (root : RawRoot) (s : State) : State :=
  match s.2 with
  | none => s
  | some (q,w,r) =>
    match unpackNode w with
    | none => (false,none)
    | some (0,[payload]) => (root q payload r,none)
    | some (tag,ws) => (false,next tag ws q r)

def iterate (root : RawRoot) : Nat → State → State
  | 0,s => s
  | fuel+1,s => iterate root fuel (tick root s)

def run (root : RawRoot) (fuel q w r : Nat) : Bool :=
  (iterate root fuel (false,some (q,w,r))).1

def raw (root : RawRoot) (q w r : Nat) : Bool :=
  let sq := (NumberedWindowSyntaxAlgorithm.syntaxBits q).1
  let sr := (NumberedWindowSyntaxAlgorithm.syntaxBits r).1
  sq && sr && run root w q w r

def windowStep (root : RawRoot) (window : Window) (ctx : List Nat) (ty q w r : Nat) : Bool :=
  raw root q w r && window ctx ty q && window ctx ty r

end LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
