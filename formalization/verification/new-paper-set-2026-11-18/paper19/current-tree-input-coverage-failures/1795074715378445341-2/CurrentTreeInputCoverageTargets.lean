module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageTargets

open LogicLineages.OrdinalComparison.Source GroundEquivalence RawSourceDAG
open CurrentTreeInputCoverage

/-- Literal all-tree admission under every original binder depth and result
type, with earlier references unchanged even when the table has repetitions. -/
def ActualTypedBuild : Prop :=
  ∀ (Γ Δ : List Ty) (τ : Ty) (t : OriginalTerm (Δ ++ Γ) τ) (ss : List Spec) (d : DAG Γ ss),
    let r := build t d
    r.graph.values (.here : Ref ((Δ,τ) :: r.tail) (Δ,τ)) = t ∧
    ∀ (s : Spec) (a : Ref ss s), r.graph.values (r.keep a) = d.values a

/-- Each exact original tree code is accepted by the actual raw program,
with the same typing/free variables, literal typed DAG code, and unchanged
tree code under the existing checked expansion. -/
def ActualTreeCodes : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  (input t).term = t ∧
  compile (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
    some (encode ⟨Γ,τ,input t⟩) ∧
  CurrentTreeCode.expand (encode ⟨Γ,τ,input t⟩) = SyntaxCode.encodeTerm t

/-- The exact checker guard and all-code total effectivity of the literal
tree conversion, including when an original input code is rejected. -/
def ActualRawProgram : Prop :=
  (∀ (Γ : List Nat) (c : Nat), compile Γ c = none ↔ SyntaxCode.check Γ c = none) ∧
  Computable₂ compile

def Full : Prop := ActualTypedBuild ∧ ActualTreeCodes ∧ ActualRawProgram

end LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageTargets
