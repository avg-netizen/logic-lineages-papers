module
public import LogicLineages.PersistentMarking.NativeTowerEraseCodeKernel

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerIteratorCodeKernel
open NativeTowerTypeCodeTargets (codecPair typeCode)
open NativeTowerEraseCodeKernel (code2 fields2 boundCode lambdaCode eraseCode)

def arrowCode (a b : Nat) : Nat := codecPair a b + 1

def applicationCode (a b f x : Nat) : Nat :=
  code2 4 (codecPair 4 (codecPair a b)) (fields2 f x)

def zeroCode : Nat := code2 4 (codecPair 0 0) 0

def recHeadCode (a : Nat) : Nat := code2 4 (codecPair 3 a) 0

def recursorCode (a z k u : Nat) : Nat :=
  let endo := arrowCode a a
  let step := arrowCode 0 endo
  applicationCode a a
    (applicationCode step endo
      (applicationCode 0 (arrowCode step endo) (recHeadCode a) z) k) u

def discardCode (a : Nat) : Nat :=
  lambdaCode a (lambdaCode a (boundCode a 1))

def leftCode (a p : Nat) : Nat :=
  applicationCode a (arrowCode a a) (discardCode a) p

def iteratorBodyCode (n : Nat) : Nat :=
  let a := typeCode n
  let e := typeCode (n+1)
  let step := applicationCode e e (leftCode e (boundCode e 2)) (eraseCode (n+1) 3)
  recursorCode a zeroCode (lambdaCode 0 step) (boundCode a 0)

def iteratorCode (n : Nat) : Nat :=
  lambdaCode (typeCode 0)
    (lambdaCode (typeCode (n+1)) (lambdaCode (typeCode n) (iteratorBodyCode n)))

end LogicLineages.PersistentMarking.NativeTowerIteratorCodeKernel
