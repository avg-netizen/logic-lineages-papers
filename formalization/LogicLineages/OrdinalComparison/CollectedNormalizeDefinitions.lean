module
public import LogicLineages.OrdinalComparison.CollectedMergeDefinitions
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal bottom-up P1 collection. The total closed-fold wrapper is honestly
noncomputable here; uniform computability of output codes is separately owed. -/
noncomputable def collectedPositiveNormalize : FixedLimitPositiveExpr → CollectedPositiveNF
  | .constant n => .mk n 0 .nil
  | .input => .mk 0 1 .nil
  | .add E F => collectedPositiveAdd (collectedPositiveNormalize E) (collectedPositiveNormalize F)
  | .head rho E =>
    let A := collectedPositiveNormalize E
    if collectedPositiveSupport A=false then
      .mk (encodedPositiveFoldValue (positiveExprEncode (.head rho E))) 0 .nil
    else .mk 0 0 (.cons rho A 1 .nil)

end LogicLineages.OrdinalComparison
