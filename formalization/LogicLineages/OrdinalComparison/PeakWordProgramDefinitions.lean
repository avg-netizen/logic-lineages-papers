module
public import LogicLineages.OrdinalComparison.PrincipalKernelWordDefinitions
public import LogicLineages.OrdinalComparison.EncodedKernelWordDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Exact finite coefficient-one expansion, on total hereditary raw codes. -/
def encodedPrincipalBlocksStep (n : Nat) (table : List (List Nat)) : List Nat :=
  if n=0 then [] else
    let p := (n-1).unpair
    List.replicate (p.2.unpair.1+1) p.1 ++ table.getD p.2.unpair.2 []

def encodedPrincipalBlocksTable : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => encodedPrincipalBlocksTable n++[encodedPrincipalBlocksStep (n+1) (encodedPrincipalBlocksTable n)]

def encodedPrincipalBlocks (n : Nat) : List Nat := (encodedPrincipalBlocksTable n).getD n []

/-- Consume coefficient-one blocks from left to right, retaining the EXACT
prefix mass and reversing their order in the literal kernel word. -/
def encodedPrincipalKernelStateStep (s : Nat × List (Nat × Nat)) (e : Nat) : Nat × List (Nat × Nat) :=
  (s.1+(1+rawNormCode e),(e,s.1)::s.2)

def encodedPrincipalWordFromBlocks (es : List Nat) (c : Nat) : List (Nat × Nat) :=
  (es.foldl encodedPrincipalKernelStateStep (c,[])).2

def encodedPrincipalPeakWord (rho : Nat) : List (Nat × Nat) :=
  encodedPrincipalWordFromBlocks (encodedPrincipalBlocks rho) 0

end LogicLineages.OrdinalComparison
