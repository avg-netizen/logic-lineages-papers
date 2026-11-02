module
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode
open Arithmetic

def numeralCode (n : Nat) := 4*n
def variableCode (i : Nat) := 4*i+1
def addCode (a b : Nat) := 4*Nat.pair a b+2
def scaleCode (n a : Nat) := 4*Nat.pair n a+3

def exprCode : Expr → Nat
  | .numeral n => numeralCode n
  | .variable i => variableCode i
  | .add a b => addCode (exprCode a) (exprCode b)
  | .scale n a => scaleCode n (exprCode a)

def liftCode (k n : Nat) : Nat :=
  if n%4=0 then n
  else if n%4=1 then variableCode (n/4+k)
  else
    let p := Nat.unpair (n/4)
    if n%4=2 then addCode (liftCode k p.1) (liftCode k p.2)
    else scaleCode p.1 (liftCode k p.2)
termination_by n
decreasing_by
  all_goals have h := Nat.unpair_left_le (n/4); have h' := Nat.unpair_right_le (n/4); omega

def truthCode : Nat := 0
def falsityCode : Nat := 1
def eqCode (a b : Nat) := 8*Nat.pair a b+2
def leCode (a b : Nat) := 8*Nat.pair a b+3
def observationCode (n src : Nat) (xs : List Nat) (y : Nat) :=
  8*Encodable.encode (n,src,xs,y)+4
def andCode (p q : Nat) := 8*Nat.pair p q+5
def orCode (p q : Nat) := 8*Nat.pair p q+6
def existsCode (p : Nat) := 8*p+7

def formulaCode : Formula → Nat
  | .truth => truthCode
  | .falsity => falsityCode
  | .eq a b => eqCode (exprCode a) (exprCode b)
  | .le a b => leCode (exprCode a) (exprCode b)
  | .observation (Γ:=Γ) _ t xs y =>
      observationCode Γ.length (SyntaxCode.encodeTerm t) (xs.map exprCode) (exprCode y)
  | .and p q => andCode (formulaCode p) (formulaCode q)
  | .or p q => orCode (formulaCode p) (formulaCode q)
  | .existsNat p => existsCode (formulaCode p)

def conjunctionCode (xs : List Nat) := xs.foldr andCode truthCode
def disjunctionCode (xs : List Nat) := xs.foldr orCode falsityCode

def successorCode (a b : Nat) := observationCode 1
  (SyntaxCode.encodeTerm (successorProbe (Γ:=[Ty.ground]) .here)) [a] b

def phiCode (a b : Nat) := orCode
  (disjunctionCode ((List.range 4).map fun i =>
    andCode (eqCode a (numeralCode i)) (eqCode b (numeralCode (Phi i)))))
  (existsCode (andCode (eqCode (liftCode 1 a) (addCode (variableCode 0) (numeralCode 4)))
    (successorCode (variableCode 0) (liftCode 1 b))))

def phiChainCode : Nat → Nat → Nat → Nat
  | 0,a,b => eqCode b a
  | n+1,a,b => existsCode (andCode (phiCode (liftCode 1 a) (variableCode 0))
      (phiChainCode n (variableCode 0) (liftCode 1 b)))
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode
