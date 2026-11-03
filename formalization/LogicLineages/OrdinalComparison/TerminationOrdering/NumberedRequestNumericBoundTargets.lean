module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestNumericBoundTargets
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedRequestWeight

/-- The accepted literal natural-number code gives a sufficient node-count bound. -/
def ActualCodeWeightBound : Prop := ∀ (n : Nat) (code : Code (Fin n)),
  codeWeight code ≤ codeNumber code + 1

/-- This sufficient numerical bound uses the accepted Code presentation. -/
def ActualCodeFuelPrimitive : Prop := ∀ (n : Nat),
  Primrec (fun code : Code (Fin n) => codeNumber code + 1)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestNumericBoundTargets
