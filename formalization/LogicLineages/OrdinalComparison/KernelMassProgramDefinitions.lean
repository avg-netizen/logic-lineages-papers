module
public import LogicLineages.OrdinalComparison.KernelMassKeyDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Test the actual faithful raw codes of exponents one and two. Every other
exponent uses its literal mass. No guessed numeric encoding is built in. -/
def encodedPrincipalKernelMassKey (eta c : Nat) : Nat :=
  if eta=rawNoteEncode (ONote.ofNat 1) then 0
  else if eta=rawNoteEncode (ONote.ofNat 2) then (c+1)/2 else c

/-- A conservative explicitly primitive-recursive upper bound on the
ORIGINAL source strict-mass threshold; the original threshold is retained. -/
def encodedStrictMassSyntaxBound (eta : Nat) : Nat := 10+2*rawNormCode eta

def encodedPrincipalKernelMassModulus (eta c e : Nat) : Nat :=
  max 1 (max (encodedStrictMassSyntaxBound eta) (max c e+1+rawNormCode eta))

def encodedPrincipalKernelMassCompare (eta c e : Nat) : Nat :=
  if encodedPrincipalKernelMassKey eta e<encodedPrincipalKernelMassKey eta c then 0
  else if encodedPrincipalKernelMassKey eta c<encodedPrincipalKernelMassKey eta e then 2 else 1

end LogicLineages.OrdinalComparison
