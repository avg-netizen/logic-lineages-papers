module
public import LogicLineages.PersistentMarking.NativeTowerExtractorCodeKernel

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerEffectiveCodeKernel
open NativeTowerTypeCodeTargets (typeCode)
open NativeTowerIteratorCodeKernel (applicationCode)
open NativeTowerExtractorCodeKernel (extractorCode)

/-- The only fixed code fields: original Fix, N_B, omega carrier. -/
abbrev Fixed := Nat × Nat × Nat

def homogeneous (j f x : Nat) : Nat := applicationCode (typeCode j) (typeCode j) f x

def lowerStep (fix j head : Nat) : Nat :=
  homogeneous (j+2) head (extractorCode fix j)

def lower (fix n head : Nat) : Nat := (List.range n).foldr (lowerStep fix) head

def zero (c : Fixed) : Nat := homogeneous 0 c.2.1 c.2.2

def later (c : Fixed) (j : Nat) : Nat :=
  homogeneous 0
    (homogeneous 1 (lower c.1 j (extractorCode c.1 j)) c.2.1)
    (zero c)

def generate (c : Fixed) (n : Nat) : Nat :=
  if n = 0 then zero c
  else if n = 1 then homogeneous 0 c.2.1 (zero c)
  else later c (n-2)

end LogicLineages.PersistentMarking.NativeTowerEffectiveCodeKernel
