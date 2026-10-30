module
public import LogicLineages.OrdinalComparison.ControlledStepProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal number of nonfinite norm-maximal replacements under the supplied
control. The well-founded call uses the proved actual source descent inequality,
not an assumed accessibility/termination field. Outside epsilon zero is zero. -/
noncomputable def actualControlledCount (g : Nat → Nat) : Ordinal.{0} → Nat :=
  Ordinal.lt_wf.fix fun a rec =>
    if ha : a < epsilonZero then
      if hn : a < Ordinal.omega0 then 0
      else rec (actualControlledStep g a)
        (actualControlledStepStrict g a (le_of_not_gt hn) ha) + 1
    else 0

end LogicLineages.OrdinalComparison
