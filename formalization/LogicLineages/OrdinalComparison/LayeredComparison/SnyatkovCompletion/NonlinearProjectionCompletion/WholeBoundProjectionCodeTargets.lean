module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeTargets
open WholeBoundProjectionCode

/-- Literal equality to the existing whole-bound initializer/projector wrapper
for every runtime list, with no Nodup, ZeroShift or valuation hypothesis. -/
def LiteralInitializedProjection : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  project bound p.encode = (WholeBoundInitialization.project bound p).encode

/-- One closed all-code program, jointly in the whole bound list and source
code, including duplicates and the inherited malformed-payload extension. -/
def ActualJointProgram : Prop := Computable₂ project

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeTargets
