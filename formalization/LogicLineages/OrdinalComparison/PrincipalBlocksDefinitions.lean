module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Executable coefficient-one CNF expansion; raw input is total, and validity
of its principal decomposition is certified separately for normal inputs.
Paper07 lem:peakword expands coefficients before deleting blocks right to left. -/
def principalExponentBlocks : ONote → List ONote
  | .zero => []
  | .oadd e n tail => List.replicate n.val e ++ principalExponentBlocks tail

/-- Literal unary additive norm of the extracted principal blocks. -/
def principalBlocksWeight (es : List ONote) : Nat :=
  (es.map fun e => 1 + Vendor.R1.treeWeight e).sum

end LogicLineages.OrdinalComparison
