module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
open LogicLineages.OrdinalComparison.Source
open Operations
/-- Literal node constructor on type codes, with empty local prefix. -/
def rawNode (t tag : Nat) (args : List Nat) : Node := ([],t,tag,args)
def applicationRaw (t : Nat) (f a : Code) : Code :=
  (f.1,rawNode t 1 [a.2.2.2,a.2.1.length+f.2.2.1,a.2.2.1] ::
    appendTable f.2.1 a.2.1,0,t)
def eraserRaw (a b : Code) : Code :=
  (a.1,rawNode 0 1 [0,0,1+b.2.2.1] ::
    rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,b.2.1.length+a.2.2.1] ::
    appendTable (insertTable a.2.1) b.2.1,0,0)
def applicationGuard (t : Nat) (f a : Code) : Bool :=
  valid f && valid a && decide (f.1=a.1) &&
    decide (f.2.2.2=SyntaxCode.arrowCode a.2.2.2 t)
def eraserGuard (a b : Code) : Bool :=
  valid a && valid b && decide (a.1=b.1) &&
    decide (a.2.2.2=0) && decide (b.2.2.2=0)
def application (t : Nat) (f a : Code) : Option Code :=
  if applicationGuard t f a then some (applicationRaw t f a) else none
def eraser (a b : Code) : Option Code :=
  if eraserGuard a b then some (eraserRaw a b) else none
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
