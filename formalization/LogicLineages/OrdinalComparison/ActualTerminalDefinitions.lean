module
public import LogicLineages.OrdinalComparison.ActualDescent

@[expose] public section

/-! Actual well-founded endpoint/count evaluator for paper 05.
Only nonfinite replacements are counted. A finite input returns its finite
value and zero; otherwise the literal checked descent step is followed.
Values outside epsilon zero are totalized to (0,0), without source meaning.
This uses actual ordinal well-founded recursion and makes no encoded
computability claim on a faithful finite notation code.
-/

namespace LogicLineages.OrdinalComparison

noncomputable def actualTerminalData : Ordinal.{0} → Nat × Nat :=
  Ordinal.lt_wf.fix fun a rec =>
    if ha : a < epsilonZero then
      if hn : a < Ordinal.omega0 then (a.card.toNat, 0)
      else
        let result := rec (actualDescentStep a)
          (actualDescentStepStrict a (le_of_not_gt hn) ha)
        (result.1, result.2 + 1)
    else (0, 0)

noncomputable def actualTerminalValue (a : Ordinal.{0}) : Nat := (actualTerminalData a).1
noncomputable def actualReplacementCount (a : Ordinal.{0}) : Nat := (actualTerminalData a).2

end LogicLineages.OrdinalComparison
