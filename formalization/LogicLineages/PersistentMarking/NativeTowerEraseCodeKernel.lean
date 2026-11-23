module
public import LogicLineages.PersistentMarking.NativeTowerTypeCodeKernel

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerEraseCodeKernel
open NativeTowerTypeCodeTargets (codecPair typeCode)

def fields2 (a b : Nat) : Nat := codecPair a (codecPair b 0 + 1) + 1

def code2 (tag a b : Nat) : Nat := codecPair tag (fields2 a b) + 1

def boundCode (ty slot : Nat) : Nat := code2 1 ty slot

def lambdaCode (ty body : Nat) : Nat := code2 2 ty body

def wrap (n seed : Nat) : Nat :=
  n.rec seed (fun j previous => lambdaCode (typeCode j) previous)

def eraseCode (n slot : Nat) : Nat :=
  wrap n (boundCode (typeCode 0) (slot+n))

end LogicLineages.PersistentMarking.NativeTowerEraseCodeKernel
