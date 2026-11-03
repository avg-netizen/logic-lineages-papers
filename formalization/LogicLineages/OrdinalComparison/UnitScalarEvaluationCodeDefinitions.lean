module
public import LogicLineages.OrdinalComparison.UnitHeadCodeDefinitions
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeDefinitions
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitScalarEvaluationCode
open ForwardTranslation

/-- Refusing scalar extraction after literal replacement of every component by
one. This does not evaluate an arbitrary ordinal or silently remove a collapse. -/
def scalarCode (n : Nat) : Option Nat := (OrdinalSyntax.extraction (UnitHeadCode.unitCode n)).2

/-- The established closed scalar evaluator contains actual collapse; only
computability, not primitive recursiveness of its evaluation, is claimed. -/
noncomputable def valueCode (n : Nat) : Option Nat :=
  (scalarCode n).map (fun s => scalarSyntaxValue s [])
end LogicLineages.OrdinalComparison.Source.UnitScalarEvaluationCode
