module
public import Mathlib.Computability.Primrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithms.Targets
/-- Actual integer operations under the standard public integer coding,
needed by the signed-row compiler. No alternative arithmetic semantics. -/
def SignedArithmetic : Prop :=
  Primrec (fun n:Nat=>(n:Int)) ∧ Primrec (fun z:Int=>-z) ∧
  Primrec₂ (fun a b:Int=>a+b) ∧ Primrec₂ (fun a b:Int=>a*b) ∧
  Primrec Int.natAbs ∧ Primrec Int.sign
end LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithms.Targets
