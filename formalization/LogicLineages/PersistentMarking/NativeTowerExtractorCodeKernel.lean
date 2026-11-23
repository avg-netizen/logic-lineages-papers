module
public import LogicLineages.PersistentMarking.NativeTowerIteratorCodeKernel

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerExtractorCodeKernel
open NativeTowerTypeCodeTargets (typeCode)
open NativeTowerEraseCodeKernel (boundCode lambdaCode)
open NativeTowerIteratorCodeKernel (applicationCode iteratorCode)

def ordinalZeroCode : Nat := lambdaCode 0 (boundCode 0 0)

def lowerOperandCode (j : Nat) : Nat :=
  if j=0 then ordinalZeroCode else boundCode (typeCode j) j

def drainStep (j q : Nat) : Nat :=
  applicationCode (typeCode j) (typeCode j) q (lowerOperandCode j)

def drainCode (n q : Nat) : Nat := (List.range n).foldr drainStep q

def appliedCode (n i h x : Nat) : Nat :=
  applicationCode (typeCode n) (typeCode n)
    (applicationCode (typeCode (n+1)) (typeCode (n+1))
      (applicationCode (typeCode 0) (typeCode (n+2)) (iteratorCode n) i) h) x

def innerCode (n : Nat) : Nat :=
  drainCode n (appliedCode n (boundCode (typeCode 0) 0)
    (boundCode (typeCode (n+1)) (n+1)) (lowerOperandCode n))

def binderStep (q j : Nat) : Nat := lambdaCode (typeCode j) q

def bindAscendingCode (count first q : Nat) : Nat :=
  ((List.range count).map (first+·)).foldl binderStep q

/-- The varying arithmetic program with the same fixed original Fix code
as a supplied numerical constant. The legacy bridge instantiates it. -/
def extractorCode (fix n : Nat) : Nat :=
  bindAscendingCode (n+1) 1
    (applicationCode (typeCode 1) (typeCode 1) fix (lambdaCode (typeCode 0) (innerCode n)))

end LogicLineages.PersistentMarking.NativeTowerExtractorCodeKernel
