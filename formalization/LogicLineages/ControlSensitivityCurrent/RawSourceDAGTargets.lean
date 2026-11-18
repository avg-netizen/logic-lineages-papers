module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAGTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence RawSourceDAG
/-- Index lookup returns the very same dependent typed variable/reference, not its denotation. -/
def References : Prop :=
  (∀ (Γ : List Ty) (τ : Ty) (x : Variable Γ τ), getVariable Γ τ (variableIndex x) = some x) ∧
  (∀ (ss : List Spec) (s : Spec) (r : Ref ss s), getReference ss s (referenceIndex r) = some r)
/-- Every actual vertex, unused/repeated references and root survive dependent typed decoding. -/
def TypedRoundtrip : Prop :=
  (∀ (Γ : List Ty) (ss : List Spec) (g : DAG Γ ss), decodeGraph Γ (encodeGraph g) = some ⟨ss,g⟩) ∧
  ∀ d : Packed, decode (encode d) = some d
/-- Validator soundness, all typed inputs accepted, exact canonical raw data and failure behavior. -/
def Validation : Prop :=
  (∀ (c : Code) (d : Packed), decode c = some d → encode d = c) ∧
  (∀ c : Code, valid c = true ↔ ∃ d : Packed, encode d = c) ∧
  (∀ d : Packed, valid (encode d) = true) ∧
  (∀ c : Code, reifyCode c = if valid c then some c else none) ∧
  (∀ (Γ : List Ty) (a : Node) (g : Graph Γ), 7 ≤ a.2.2.1 → step Γ a g = none)
/-- Exact table node count plus genuine computable validation/reification on finite raw codes.
The reifier is concretely decode followed by encode; it is not an assumed choice function. -/
def Effective : Prop :=
  (∀ (Γ : List Ty) (ss : List Spec) (g : DAG Γ ss), (encodeGraph g).length = ss.length) ∧
  Computable valid ∧ Computable reifyCode
end LogicLineages.ControlSensitivityCurrent.RawSourceDAGTargets
