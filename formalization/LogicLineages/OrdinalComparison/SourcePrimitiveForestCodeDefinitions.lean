module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode
open PrimitiveLowering

/-- Port numbers are distinct from source codes: zero denotes literal zero. -/
def portNumber {Γ} : Port Γ → Nat
  | .zero => 0
  | .var x => SourceTypedPorts.variableIndex x+1
def shiftPort (k p : Nat) : Nat := if p=0 then 0 else p+k
def portCode (p : Nat) : Nat := if p=0 then 1 else 8*(p-1)
def successorCode (p : Nat) : Nat := 8*Nat.pair 2 (portCode p)+5
def eraserCode (p q : Nat) : Nat := SourceGammaAggregateCode.eraserCode (portCode p) (portCode q)
def identityZeroCode : Nat := 8*Nat.pair (8*Nat.pair 0 0+6) 1+5

def expressionCode {Γ} : Expr Γ → Nat
  | .port a => portCode (portNumber a)
  | .successor a => successorCode (portNumber a)
  | .erase a b => eraserCode (portNumber a) (portNumber b)
  | .identityZero => identityZeroCode

def addPairs (a b c d : Nat) : List (Nat×Nat) :=
  [(eraserCode b 0,eraserCode 0 d),(eraserCode a d,eraserCode c 0)]
def unusedPairs (start : Nat) : List (Nat×Nat) :=
  ((List.range 9).filter (fun i => start ≤ i)).map (fun i => (portCode (i+1),1))
def eqForest (a b : Nat) : List (Nat×Nat) :=
  (portCode (shiftPort 9 a),portCode (shiftPort 9 b))::unusedPairs 0
def addForest (a b c : Nat) : List (Nat×Nat) :=
  addPairs (shiftPort 9 a) (shiftPort 9 b) (shiftPort 9 c) 1 ++ unusedPairs 1
def oneForest (a : Nat) : List (Nat×Nat) :=
  (successorCode 1,identityZeroCode)::
    (addPairs (shiftPort 9 a) (shiftPort 9 a) 1 2 ++ unusedPairs 2)
def forestCodes {Γ} (g : Gate Γ) : List (Nat×Nat) :=
  (forest g).map (fun f => (SyntaxCode.encodeTerm f.1.term,SyntaxCode.encodeTerm f.2.term))
end LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode
