module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
open LogicLineages.OrdinalComparison.Source
open Operations CheckedComposition

def detectorLeftRaw (a b : Code) : Code := eraserRaw (eraserRaw a a) (eraserRaw b b)
def detectorRightRaw (a b : Code) : Code := eraserRaw (eraserRaw a b) (eraserRaw b a)
def detectors (a b : Code) : Option (Code × Code) :=
  if eraserGuard a b then some (detectorLeftRaw a b,detectorRightRaw a b) else none
def zeroRaw (Γ : List Nat) : Code := (Γ,[rawNode 0 3 []],0,0)
def aggregateRaw (Γ : List Nat) : List (Code × Code) → Code × Code
  | [] => (zeroRaw Γ,zeroRaw Γ)
  | (a,b)::es =>
      let tail := aggregateRaw Γ es
      (eraserRaw (detectorLeftRaw a b) tail.1,eraserRaw (detectorRightRaw a b) tail.2)
def aggregateGuard (Γ : List Nat) (es : List (Code × Code)) : Bool :=
  es.foldr (fun p ok => eraserGuard p.1 p.2 && decide (p.1.1=Γ) && ok) true
def aggregate (Γ : List Nat) (es : List (Code × Code)) : Option (Code × Code) :=
  if aggregateGuard Γ es then some (aggregateRaw Γ es) else none

/-- Actual magnifyInput vertex order: application, zero, lambda, inserted input. -/
def magnifyRaw (c : Code) : Code :=
  (c.1,rawNode 0 1 [0,1,0] :: rawNode 0 3 [] ::
    rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,c.2.2.1] :: insertTable c.2.1,0,0)
/-- Actual identityInput: application, lambda, locally bound variable, input. -/
def identityRaw (c : Code) : Code :=
  (c.1,rawNode 0 1 [0,0,2+c.2.2.1] :: rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,0] ::
    ([0],0,0,[0]) :: c.2.1,0,0)
/-- Actual constantInput: application, lambda, local-prefix zero, input. -/
def constantRaw (c : Code) : Code :=
  (c.1,rawNode 0 1 [0,0,2+c.2.2.1] :: rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,0] ::
    ([0],0,3,[]) :: c.2.1,0,0)
def wrapperRaw (upper : Bool) (c : Code) : Code :=
  if upper then constantRaw (magnifyRaw c) else identityRaw (magnifyRaw c)
def wrapperGuard (c : Code) : Bool := valid c && decide (c.2.2.2=0)
def wrap (upper : Bool) (c : Code) : Option Code :=
  if wrapperGuard c then some (wrapperRaw upper c) else none
def rawWeight (es : List (Code × Code)) : Nat :=
  (es.map (fun p => 2*(p.1.2.1.length+p.2.2.1.length)+8)).sum+1
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
