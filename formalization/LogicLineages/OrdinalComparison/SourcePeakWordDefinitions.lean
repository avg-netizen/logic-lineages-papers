module
public import LogicLineages.OrdinalComparison.PrincipalBlocksProof
public import LogicLineages.OrdinalComparison.PeakWordProgramDefinitions
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsDefinitions
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions
public import LogicLineages.OrdinalComparison.CollectedPeakDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Original principal blocks with only their already-proved normality
certificates attached. No new notation, quotient or semantic representative. -/
def comparisonTypedPrincipalBlocks (rho : NONote) : List NONote :=
  (principalExponentBlocks rho.1).attach.map (fun e =>
    ⟨e.1,(actualPrincipalBlocksNormalOrder rho.1 rho.2).1 e.1 e.2⟩)

def comparisonTypedPrincipalWord : List NONote → Nat → List (NONote × Nat)
  | [],_ => []
  | e::es,c => comparisonTypedPrincipalWord es (c+(1+Vendor.R1.treeWeight e.1))++[(e,c)]

def comparisonSourcePeakWord (rho : NONote) (E : FixedLimitPositiveExpr) : OneVariableComparisonExpr :=
  .range (comparisonTypedPrincipalWord (comparisonTypedPrincipalBlocks rho) 0)
    (.add E (.constant (Vendor.R1.treeWeight rho.1)))

def encodedSourcePeakWord (rho arg : Nat) : Nat :=
  2*Nat.pair (Encodable.encode (encodedPrincipalPeakWord rho))
    (4*Nat.pair arg (4*rawNormCode rho)+2)+1

def comparisonLiteralSourceHeadCount : OneVariableComparisonExpr → Nat
  | .positive E | .range _ E => comparisonPositiveSourceHeadCount E

end LogicLineages.OrdinalComparison
