from pathlib import Path
out=Path('LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalBetaPairArithmeticProof.lean')
def add(a,b): return (a,b)
def fmt(t): return t if isinstance(t,str) else f'(add {fmt(t[0])} {fmt(t[1])})'
def refl(t): return f'(refl {fmt(t)})'
def trans(a,b): return f'(trans {a} {b})'
def left(t,p): return f'(congAddLeft {fmt(t)} {p})'
def right(t,p): return f'(congAddRight {fmt(t)} {p})'
def chain(*ps):
 r=ps[-1]
 for p in reversed(ps[:-1]): r=trans(p,r)
 return r
def rt(xs):
 if len(xs)==1:return xs[0]
 return add(xs[0],rt(xs[1:]))
def append(xs,ys):
 if len(xs)==1:return refl(add(xs[0],rt(ys)))
 return chain(f'(associativity {fmt(xs[0])} {fmt(rt(xs[1:]))} {fmt(rt(ys))})',left(xs[0],append(xs[1:],ys)))
def flatten(t):
 if isinstance(t,str):return [t],refl(t)
 xs,p=flatten(t[0]);ys,q=flatten(t[1])
 return xs+ys,chain(right(t[1],p),left(rt(xs),q),append(xs,ys))
def swap(xs,i):
 if i: return left(xs[0],swap(xs[1:],i-1))
 a,b,*tail=xs
 if not tail:return f'(commutativity {a} {b})'
 c=rt(tail)
 return chain(f'(symm (associativity {a} {b} {fmt(c)}))',right(c,f'(commutativity {a} {b})'),f'(associativity {b} {a} {fmt(c)})')
def norm(t):
 xs,p=flatten(t)
 for j in range(len(xs)):
  for i in range(len(xs)-1):
   if xs[i]>xs[i+1]:
    p=trans(p,swap(xs,i));xs[i],xs[i+1]=xs[i+1],xs[i]
 return p
P='p';x='x';y='y';A=add(y,y);S=add(x,y)
L=add(add(add(add(P,P),S),add(A,A)),x)
R=add(add(add(add(P,P),add(S,S)),A),y)
B=add(y,add(add(x,x),y));C=add(S,S)
preamble='''module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalMultiplicationLeftSuccessorProof InternalQuotientGapProof
open InternalBetaPairCode
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def oneMul (t : OTerm α) : Derivation body Gamma (eqn (mul (suc z) t) t) :=
  trans (leftSuccessorMultiplication z t)
    (trans (congAddRight t (multiplicationLeftZero t)) (leftZero t))
def twoMul (t : OTerm α) : Derivation body Gamma (eqn (mul (suc (suc z)) t) (twice t)) :=
  trans (leftSuccessorMultiplication (suc z) t) (congAddRight t (oneMul t))

/-- A finite composition of original associativity/commutativity derivations. -/
def rearrangePair (p x y : OTerm α) : Derivation body Gamma
'''
s=preamble+f'    (eqn {fmt(L)} {fmt(R)}) :=\n  {trans(norm(L),f"(symm {norm(R)})")}\n\n'
s+='''def pairEquation (x y : OTerm α) : Derivation body Gamma
    (eqn (firstCode x y) (add (mul (secondQuotient y) (suc (twice (secondCode x y)))) y)) := by
  let a := twice y
  let s := secondCode x y
  let p := mul a s
  have hl : Derivation body Gamma
      (eqn (firstCode x y) (suc (add (add (add (add p p) s) (add a a)) x))) :=
    trans (congAddRight x (mulSucc (suc (add a a)) s))
      (trans (congAddRight x (congAddRight (suc (add a a)) (leftSuccessorMultiplication (add a a) s)))
        (trans (congAddRight x (congAddRight (suc (add a a)) (congAddRight s (leftDistributivity a a s))))
          (trans (congAddRight x (addSucc (add (add p p) s) (add a a)))
            (leftSuccessor (add (add (add p p) s) (add a a)) x))))
  have hr : Derivation body Gamma
      (eqn (add (mul (secondQuotient y) (suc (twice s))) y)
        (suc (add (add (add (add p p) (add s s)) a) y))) :=
    trans (congAddRight y (mulSucc (suc a) (add s s)))
      (trans (congAddRight y (congAddRight (suc a) (leftSuccessorMultiplication a (add s s))))
        (trans (congAddRight y (congAddRight (suc a) (congAddRight (add s s) (distributivity a s s))))
          (trans (congAddRight y (addSucc (add (add p p) (add s s)) a))
            (leftSuccessor (add (add (add p p) (add s s)) a) y))))
  exact trans hl (trans (congSuc (rearrangePair p x y)) (symm hr))

def rearrangeBound (x y : OTerm α) : Derivation body Gamma
'''
s+=f'    (eqn {fmt(B)} {fmt(C)}) :=\n  {trans(norm(B),f"(symm {norm(C)})")}\n\n'
s+='''def boundEquation (x y : OTerm α) : Derivation body Gamma
    (eqn (add y (suc (add (twice x) y))) (suc (twice (secondCode x y)))) :=
  trans (addSucc y (add (twice x) y)) (congSuc (rearrangeBound x y))

theorem actualPairEquation : InternalBetaPairArithmeticTargets.ActualPairEquation := by
  intro body α Gamma x y
  rw [onEquality]
  exact ⟨pairEquation x y⟩
theorem actualOneMultiplication : InternalBetaPairArithmeticTargets.ActualOneMultiplication := by
  intro body α Gamma t
  rw [onEquality]
  exact ⟨oneMul t⟩
theorem actualTwoMultiplication : InternalBetaPairArithmeticTargets.ActualTwoMultiplication := by
  intro body α Gamma t
  rw [onEquality]
  exact ⟨twoMul t⟩
theorem actualBoundEquation : InternalBetaPairArithmeticTargets.ActualBoundEquation := by
  intro body α Gamma x y
  rw [onEquality]
  exact ⟨boundEquation x y⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticProof
'''
out.write_text(s)
