module
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Append one actual kernel to the OUTSIDE of a source-word code. The
numeric function is total even at malformed source codes. -/
def encodedComparisonAppendKernel (n eta c : Nat) : Nat :=
  let p := (n/2).unpair
  let w := (Encodable.decode (α := List (Nat × Nat)) p.1).getD []
  2*Nat.pair (Encodable.encode (w++[(eta,c)])) p.2+1

def successorExpandedWord (w : List (NONote × Nat)) (eta pred : NONote) (c : Nat) :
    List (NONote × Nat) :=
  w++[(eta,c+1+Vendor.R1.treeWeight pred.1),(pred,c)]

/-- Source successor cut keeps its higher kernel internally, with its
literal increased retained mass, and exposes the predecessor kernel. -/
def encodedSuccessorWordExpansion (n eta pred c : Nat) : Nat :=
  encodedComparisonAppendKernel (encodedComparisonAppendKernel n eta (c+1+rawNormCode pred)) pred c

def encodedSuccessorWordTail (n eta pred c : Nat) : Nat :=
  max (encodedOneVariableComparisonDomainBound (encodedComparisonAppendKernel n eta c))
    (encodedOneVariableComparisonDomainBound (encodedSuccessorWordExpansion n eta pred c))

end LogicLineages.OrdinalComparison
