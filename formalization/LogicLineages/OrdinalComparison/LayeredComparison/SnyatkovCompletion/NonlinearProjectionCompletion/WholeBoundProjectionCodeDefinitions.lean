module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCode

/-- The original whole-bound wrapper: initialize the actual normal-form code
for the same runtime bound list, then execute the original numeric projector.
No syntax test, semantic witness or supplied solver changes either program. -/
def project (bound : List Nat) (code : Nat) : Nat :=
  PlainBlockProjectionCode.project bound (WholeBoundInitializationCode.formula bound code)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCode
