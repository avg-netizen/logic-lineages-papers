module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence

theorem variable_roundtrip {Γ τ} (x : Variable Γ τ) :
    getVariable Γ τ (variableIndex x) = some x := by
  induction x with
  | here => simp [variableIndex,getVariable]
  | there x ih => simp [variableIndex,getVariable,ih]

theorem reference_roundtrip {ss s} (r : Ref ss s) :
    getReference ss s (referenceIndex r) = some r := by
  induction r with
  | here => simp [referenceIndex,getReference]
  | there r ih => simp [referenceIndex,getReference,ih]

theorem references : RawSourceDAGTargets.References :=
  ⟨fun _ _ x => variable_roundtrip x,fun _ _ r => reference_roundtrip r⟩

@[simp] theorem decode_type (τ : Ty) : SyntaxCode.decodeType (SyntaxCode.typeCode τ) = τ :=
  SyntaxCode.Proof.typeDecodeEncode τ
@[simp] theorem encode_type (n : Nat) : SyntaxCode.typeCode (SyntaxCode.decodeType n) = n :=
  SyntaxCode.Proof.typeEncodeDecode n

theorem decode_types (Γ : List Ty) :
    (Γ.map SyntaxCode.typeCode).map SyntaxCode.decodeType = Γ := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih => simp [decode_type,ih]

theorem encode_types (Γ : List Nat) :
    (Γ.map SyntaxCode.decodeType).map SyntaxCode.typeCode = Γ := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih => simp [encode_type,ih]

theorem graph_roundtrip {Γ ss} (g : DAG Γ ss) :
    decodeGraph Γ (encodeGraph g) = some ⟨ss,g⟩ := by
  induction g with
  | nil => rfl
  | var d x ih =>
      simp [encodeGraph,decodeGraph,ih,step,node,decode_types,
        decode_type,variable_roundtrip]
  | app d f a ih =>
      simp [encodeGraph,decodeGraph,ih,step,node,decode_types,
        decode_type,reference_roundtrip]
  | lam d b ih =>
      simp [encodeGraph,decodeGraph,ih,step,node,decode_types,
        decode_type,reference_roundtrip]
  | zero d ih =>
      simp [encodeGraph,decodeGraph,ih,step,node,decode_types,
        SyntaxCode.Proof.typeDecodeEncode]
  | succ d ih =>
      simp [encodeGraph,decodeGraph,ih,step,node,decode_types,
        SyntaxCode.Proof.typeDecodeEncode]
  | case d τ ih =>
      simp [encodeGraph,decodeGraph,ih,step,node,decode_types,
        SyntaxCode.Proof.typeDecodeEncode]
  | recursor d τ ih =>
      simp [encodeGraph,decodeGraph,ih,step,node,decode_types,
        SyntaxCode.Proof.typeDecodeEncode]

theorem input_roundtrip (d : Packed) : decode (encode d) = some d := by
  rcases d with ⟨Γ,τ,⟨ss,g,r⟩⟩
  simp only [encode,decode,decode_types,decode_type,graph_roundtrip,Option.bind_some,reference_roundtrip]

theorem typedRoundtrip : RawSourceDAGTargets.TypedRoundtrip :=
  ⟨fun _ _ g => graph_roundtrip g,input_roundtrip⟩

theorem graph_length {Γ ss} (g : DAG Γ ss) : (encodeGraph g).length = ss.length := by
  induction g <;> simp_all [encodeGraph]

theorem typedAccepted (d : Packed) : valid (encode d) = true := by
  simp [valid,input_roundtrip]
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG
