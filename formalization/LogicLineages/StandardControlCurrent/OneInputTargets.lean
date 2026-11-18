module
public import LogicLineages.OrdinalComparison.OneInputBooleanDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.OneInputTargets
open OrdinalComparison

/-- Complete current18 u:cor:boolean, with effective literal postfix source
translation, original-source prefix evaluation, common tail and both closures. -/
def OneInputQuantifiedComparison : Prop :=
  (Computable₂ encodedOneInputBooleanValue ∧
    Computable encodedOneInputBooleanTail ∧ Computable encodedOneInputBooleanClosures) ∧
  (∀ formula : OneInputBooleanExpr, oneInputBooleanValid formula →
    ∀ x : Nat, encodedOneInputBooleanValue (oneInputBooleanCompile formula) x =
      actualOneInputBooleanValue formula x) ∧
  (∀ formula : OneInputBooleanExpr, oneInputBooleanValid formula →
    let N := encodedOneInputBooleanTail (oneInputBooleanCompile formula)
    1 ≤ N ∧ ∀ x : Nat, N ≤ x →
      actualOneInputBooleanValue formula x = actualOneInputBooleanValue formula N) ∧
  ∀ formula : OneInputBooleanExpr, oneInputBooleanValid formula →
    let flags := encodedOneInputBooleanClosures (oneInputBooleanCompile formula)
    (flags.1 = true ↔ ∃ x : Nat, 0 < x ∧ actualOneInputBooleanValue formula x = true) ∧
    (flags.2 = true ↔ ∀ x : Nat, 0 < x → actualOneInputBooleanValue formula x = true)

end LogicLineages.StandardControlCurrent.OneInputTargets
