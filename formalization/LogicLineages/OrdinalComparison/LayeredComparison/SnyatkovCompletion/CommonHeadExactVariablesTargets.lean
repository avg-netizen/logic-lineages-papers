module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesTargets
open CommonLayerSyntax CommonLayerComparison CommonHeadExactVariables

/-- All raw inputs, including zero, malformed payloads, empty heads/sums and
impossible desired signs. Equality means the free-variable SET, not occurrence order. -/
def RawTruthAndExactSupport : Prop := ∀ heads E F desired,
  (∀ ν, (formula heads E F desired).eval ν ↔ (compile heads E F desired).eval ν) ∧
  (∀ i, i ∈ (formula heads E F desired).variables ↔
    i ∈ codedVariables heads.length E ++ codedVariables heads.length F)

/-- Literal code equality on every raw input, so no reinterpreted syntax is used. -/
def LiteralCodeCalibration : Prop := ∀ p : Input,
  output p = (formula p.1 p.2.1 p.2.2.1 p.2.2.2).encode

/-- The first sentence of paper08 thm:common, for actual source syntax and
actual fixed nonzero limit heads at ONE original raw valuation. Stronger than
the positive-valuation restriction. The full quantified-decision sentence is NOT claimed. -/
def ActualSourceClause : Prop := ∀ Γ : List NONote, genuineHeads Γ →
  ∀ (E F : CommonSyntax Γ.length) (desired : Int),
  (∀ ν, BaseFormula.evaluate ν
    (output (headCodes Γ, encodeCommon Γ.length E, encodeCommon Γ.length F, desired)) = true ↔
    Int.sign ((commonValue Γ E ν : Int) - (commonValue Γ F ν : Int)) = desired) ∧
  (∀ i, i ∈ BaseFormula.rawVariables
    (output (headCodes Γ, encodeCommon Γ.length E, encodeCommon Γ.length F, desired)) ↔
    i ∈ commonVariables Γ.length E ++ commonVariables Γ.length F)

/-- Actual extraction on EVERY raw depth/code, with the original decoder defaults. -/
def ActualSupportProgram : Prop := Computable₂ codedVariables

/-- Actual finite output instructions are computed on every raw input. -/
def ActualOutputProgram : Prop := Computable output

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesTargets
