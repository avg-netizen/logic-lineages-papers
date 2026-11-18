module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open RawSourceDAG RawSourceDAG.PrimitiveGate PrimitiveLowering

def encodeForest {Γ : List Ty} (es : List (Input Γ .ground × Input Γ .ground)) :
    List (Code × Code) :=
  es.map fun e => (encode ⟨Γ, .ground, e.1⟩, encode ⟨Γ, .ground, e.2⟩)

def GateExactness : Prop :=
  ∀ (Γ : List Ty) (raw : GateCode),
    gateGuard (Γ.map SyntaxCode.typeCode) raw = true ↔ ∃ g : Gate Γ, encodeGate g = raw

def ForestExactness : Prop :=
  ∀ (Γ : List Ty) (g : Gate Γ),
    compile (Γ.map SyntaxCode.typeCode) (encodeGate g) = some (encodeForest (forest g))

def SuccessReconstruction : Prop :=
  ∀ (context : List Nat) (raw : GateCode) (out : List (Code × Code)),
    compile context raw = some out →
    ∃ (Γ : List Ty) (g : Gate Γ), Γ.map SyntaxCode.typeCode = context ∧
      encodeGate g = raw ∧ out = encodeForest (forest g) ∧
      ∀ e ∈ forest g,
        decode (encode ⟨Block Γ, .ground, e.1⟩) = some ⟨Block Γ, .ground, e.1⟩ ∧
        decode (encode ⟨Block Γ, .ground, e.2⟩) = some ⟨Block Γ, .ground, e.2⟩

def RejectionAndCounts : Prop :=
  (∀ (context : List Nat) (raw : GateCode), compile context raw = none ↔ gateGuard context raw = false) ∧
  ∀ (context : List Nat) (raw : GateCode) (out : List (Code × Code)),
    compile context raw = some out → out.length = 10 ∧
      ∀ e ∈ out, valid e.1 = true ∧ valid e.2 = true ∧
        e.1.1 = blockContext context ∧ e.2.1 = blockContext context

def Effective : Prop :=
  Computable (fun p : List Nat × GateCode => compile p.1 p.2)

end LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateTargets
