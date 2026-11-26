module

public import LogicLineages.PersistentMarking.NumberedWindowShiftAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowSingletonAlgorithm
open NumberedWindowFieldAlgorithm (packNode unpackNode)
open NumberedWindowShiftAlgorithm (Table Row argsNext)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

/-- One bound slot is removed at the actual ambient depth. A hit shifts the
inserted term past every intervening binder. -/
def termParts (t : Table) (inserted depth offset tag : Nat) (fs : List Nat) : Nat :=
  if tag = 1 then
    let d := depth + offset
    let i := fs.getD 1 0
    if i < d then packNode 1 fs else if i = d then
      ((NumberedWindowShiftAlgorithm.output d 0 inserted).1).getD 0
    else packNode 1 [fs.getD 0 0,i.pred]
  else NumberedWindowShiftAlgorithm.termParts t 0 depth offset tag fs

def next (inserted depth offset n : Nat) (t : Table) : Row :=
  (((unpackNode n).map (fun p => termParts t inserted depth offset p.1 p.2)).getD 0,
    argsNext offset n t)

def table (inserted depth bound : Nat) : Nat → Table
  | 0 => []
  | n+1 =>
    let t := table inserted depth bound n
    t ++ [(List.range (bound+1)).map (fun offset => next inserted depth offset n t)]

def computed (inserted depth bound n offset : Nat) : Row :=
  next inserted depth offset n (table inserted depth bound n)

/-- Both optional outputs reject a malformed inserted term, even when the
body happens to have no occurrence of the discharged slot. -/
def output (inserted depth n : Nat) : Option Nat × Option Nat :=
  let row := computed inserted depth n n 0
  let a := (syntaxBits inserted).1
  let valid := syntaxBits n
  (if a && valid.1 then some row.1 else none, if a && valid.2 then some row.2 else none)
end LogicLineages.PersistentMarking.NumberedWindowSingletonAlgorithm
